open Utils

type t =
  | Var of int (* De Bruijn levels, see e.g. https://link.springer.com/chapter/10.1007/3-540-59200-8_65 (also at https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/level.pdf) *)
  | Const of string
  | Fun of string * t * t
  | App of t list (* FIXME: slow *)
  | Type of Univ.t
  | Pi of string * t * t
  | Let of string * t * t * t

(* Invariant : depth = List.length var *)
type context = { depth : int; var : (string * t * t option) list; const : (t * t) SMap.t }

type type_error =
  | UnboundVar of int
  | UnboundConst of string
  | NotAType of t
  | IllegalApplication of t
  | TypeMismatch of t * t
  | IllFormed of t
  | NoBody of t

exception TypeError of context * type_error

let mkApp f args =
  match args, f with
  | [], f -> f
  | args, App f -> App (f @ args)
  | args, f -> App (f :: args)

let rec debug_print e =
  let (+) = fun _ e -> debug_print e in
  let ( ++ ) = fun _ s -> print_string s in
  match e with
  | Fun (v, t, body) -> () ++ "(fun " ++ v ++ " : " + t ++ " => " + body ++ ")"
  | Pi (v, t, body) -> () ++ "(forall " ++ v ++ " : " + t ++ ", " + body ++ ")"
  | Let (v, ty, t, body) -> () ++ "(let " ++ v ++ " : " + ty ++ " := " + t ++ " in " + body ++ ")"
  | Var v -> () ++ "Var "; print_int v
  | Const v -> () ++ "Const " ++ v
  | App (f :: a) ->
    let (+) = fun _ e -> () ++ "(" + e ++ ")" in
    () ++ "App " + f; List.iter (fun e -> () ++ " " + e) a
  | Type l ->
    let pr_atom v i =
      if v = "" then
        (if i = 0 then
          () ++ "Prop"
        else (() ++ "Type@{"; print_int i ++ "}"))
      else if i = 0 then () ++ v else (() ++ v ++ "+"; print_int i) in
    if SMap.cardinal l = 1 then
      let (v, i) = SMap.choose l in pr_atom v i
    else (() ++ "Type@{max("; SMap.iter (fun v i -> pr_atom v i ++ ", ") l ++ ")")
  | _ -> raise (TypeError ({ depth = 0; var = []; const = SMap.empty }, IllFormed e))

(* Replaces every `Var i` in `t` by `f i`, NOT avoiding capture. *)
let rec subst f t =
  match t with
  | Var i -> f i
  | Const _ | Type _ -> t
  | App l -> App (List.map (subst f) l)
  | Fun (v, ty, body) -> Fun (v, subst f ty, subst f body)
  | Pi (v, ty, body) -> Pi (v, subst f ty, subst f body)
  | Let (v, ty, t, body) -> Let (v, subst f ty, subst f t, subst f body)

(* [beta ctx t t'] beta-reduces (\lambda. t') t *)
let beta ctx t = subst (fun i -> if i = ctx.depth then t else if i < ctx.depth then Var i else Var (i-1))

module Context = struct
  type t = context

  let empty = { depth = 0; var = []; const = SMap.empty }

  let find_var ctx i =
    try List.nth ctx.var (ctx.depth-i-1) with _ -> raise (TypeError (ctx, UnboundVar i))

  let find_const ctx c =
    try SMap.find c ctx.const with _ -> raise (TypeError (ctx, UnboundConst c))

  let get_var_name ctx i = let (v, _, _) = find_var ctx i in v
  let get_var_type ctx i = let (_, ty, _) = find_var ctx i in ty
  let get_var_body ctx i =
    let (_, _, t) = find_var ctx i in
    match t with
    | None -> raise (TypeError (ctx, NoBody (Var i)))
    | Some body -> body

  let var_depth ctx = ctx.depth

  let get_const_type ctx c = subst (fun i -> Var (i + ctx.depth)) (fst (find_const ctx c))
  let get_const_body ctx c = subst (fun i -> Var (i + ctx.depth)) (snd (find_const ctx c))

  let push_var ctx t = { ctx with depth = ctx.depth+1;
    var = t :: ctx.var }

  let push_const ctx c t = { ctx with const = SMap.add c t ctx.const }

  let pop_var ctx =
    match ctx.var with
    | [] -> ctx (* TOTHINK: should I fail? *)
    | _ :: var -> { ctx with depth = ctx.depth-1; var }

  let rec pp_term ctx t =
    let ( ++ ) = fun _ s -> print_string s in
    let rec pr_telescope ctx = function
      | [] -> ctx
      | (v, t) :: args ->
        let ctx' = push_var ctx (v, t, None) in
        let () = () ++ "(" ++ v ++ " : "; pp_term ctx t ++ (if args = [] then ")" else ") ") in
        pr_telescope ctx' args in
    let rec pr_fun ctx args body =
      match body with
      | Fun (v, t, body) -> pr_fun ctx ((v, t) :: args) body
      | _ ->
        () ++ "fun ";
        let ctx = pr_telescope ctx (List.rev args) in
        () ++ ", "; pp_term ctx body in
    let rec pr_pi ctx args body =
      match body with
      | Pi (v, t, body) -> pr_pi ctx ((v, t) :: args) body
      | _ ->
        () ++ "forall ";
        let ctx = pr_telescope ctx (List.rev args) in
        () ++ ", "; pp_term ctx body in
    let atomic = function
      | Var _ | Const _ | Type _ -> true
      | _ -> false in
    match t with
    | Fun (v, t, body) -> pr_fun ctx [(v, t)] body
    | Pi (v, t, body) -> pr_pi ctx [(v, t)] body
    | Let (v, ty, t, body) -> () ++ "let " ++ v ++ " : "; pp_term ctx ty ++ " := "; pp_term ctx t ++ " in "; pp_term (push_var ctx (v, t, None)) body
    | Var v -> () ++ get_var_name ctx v
    | Const v -> () ++ v
    | App (f :: a) ->
      let (+) = fun _ e -> if atomic e then pp_term ctx e else (() ++ "("; pp_term ctx e ++ ")") in
      () + f; List.iter (fun e -> () ++ " " + e) a
    | Type l -> let pr_atom v i =
      if v = "" then
        (if i = 0 then
          () ++ "Prop"
        else (() ++ "Type@{"; print_int i ++ "}"))
      else if i = 0 then () ++ v else (() ++ v ++ "+"; print_int i) in
    if SMap.cardinal l = 1 then
      let (v, i) = SMap.choose l in pr_atom v i
    else (() ++ "Type@{max("; SMap.iter (fun v i -> pr_atom v i ++ ", ") l ++ ")")
    | _ -> raise (TypeError (empty, IllFormed t))


  let print ctx =
    print_string "CTX:\n\t Local variables:\n";
    List.iter (fun (v, ty, t) -> print_string "\t\t"; print_string v; print_string " : "; pp_term ctx ty; (match t with | None -> () | Some t -> print_string " := "; pp_term ctx t); print_string "\n") ctx.var;
    print_string "\n\t Global variables:\n";
    SMap.iter (fun v (ty, body) -> print_string "\t\t"; print_string v; print_string " : "; pp_term ctx ty; print_string " := "; pp_term ctx body; print_string "\n") ctx.const;
    print_string "\n"

end

let print = Context.pp_term

let rec occurs t t' =
  t = t' ||
  match t' with
  | Var _ | Type _ | Const _ -> false
  | App l -> List.exists (occurs t) l
  | Fun (_, ty, body) | Pi (_, ty, body) -> 
    occurs t ty || occurs (subst (fun i -> Var (i+1)) t) body
  | Let (_, ty, t', body) ->
    occurs t ty || occurs t t' || occurs (subst (fun i -> Var (i+1)) t) body

let rec whd_all ctx t =
  match t with
  | Var _ | Type _ | Pi _ -> t
  | Const c -> Context.get_const_body ctx c
  | Fun (_, _, body) -> 
    (* There is no need to change the context since we never look for variables *)
    (match whd_all ctx body with
    | App l ->
      (match List.rev l with
      | Var 0 :: l when not (occurs (Var 0) (App l)) ->
        (match List.rev l with
        | [t] -> t
        | l -> App l)
      | _ -> t) (* TOTHINK: Is losing the computation a problem? *)
    | _ -> t)
  | Let (_, _, t, body) -> whd_all ctx (beta ctx t body)
  | App (f :: l) ->
    (match whd_all ctx f, l with
    | Fun (_, _, body), x :: l -> whd_all ctx (mkApp (beta ctx x body) l)
    | h, _ -> App (h :: l))
  | _ -> raise (TypeError (ctx, IllFormed t))

let rec unify ctx t1 t2 =
  let behead h args =
    match h with
    | App (f :: l) -> f, l @ args
    | _ -> h, args in 
  let may_reduce ctx h args =
    match h with
    | Type _ | Pi _ -> false
    | Fun _ -> args <> []
    | Var i -> (try let _ = Context.get_var_body ctx i in true with _ -> false)
    | Const _ | Let _ -> true
    | _ -> failwith "Internal error : head should not by an application." in
  let beta body = function
    | [] -> failwith "Internal error : term should be applied"
    | x :: args -> behead (beta ctx x body) args in
  (* unifies t1 and t2 when t2 may reduce *)
  let rec mixed ctx (h1, args1 as t1) (h2, args2) =
    match h1, h2 with
    | h1, Fun (_, ty2, body2) ->
      (match h1 with
      | Fun (v, ty1, body1) -> unify ctx ty1 ty2 && unify (Context.push_var ctx (v, ty1, None)) body1 body2 && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (beta body2 args2)
    | h1, Let (_, ty2, t2, body2) ->
      (match h1 with
      | Let (v, ty1, t1, body1) -> unify ctx ty1 ty2 && unify ctx t1 t2 && unify (Context.push_var ctx (v, ty1, None)) body1 body2 && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (beta body2 (t2 :: args2))
    | h1, Var i2 ->
      (match h1 with
      | Var i1 -> i1 = i2 && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (behead (Context.get_var_body ctx i2) args2)
    | _, Const c -> aux ctx t1 (behead (Context.get_const_body ctx c) args2)
    | _, _ -> failwith "Internal error : non-reducible term classified as maybe reducible."
  and aux ctx (h1, args1 as t1) (h2, args2 as t2) =
    if may_reduce ctx h2 args2 then mixed ctx t1 t2 else
    if may_reduce ctx h1 args1 then mixed ctx t2 t1 else
    match h1, h2 with
    | Var i, Var j -> i = j && List.for_all2 (unify ctx) args1 args2
    | Type _, Type _ -> true (* FIXME: implement universes *)
    | Fun (v, ty1, body1), Fun (_, ty2, body2)
    | Pi (v, ty1, body1), Pi (_, ty2, body2) ->
      unify ctx ty1 ty2 && unify (Context.push_var ctx (v, ty1, None)) body1 body2 && List.for_all2 (unify ctx) args1 args2
    | _, _ -> false in
  aux ctx (behead t1 []) (behead t2 [])

let type_of ctx t =
  let rec aux ctx t =
    match t with
    | Var i -> (try Context.get_var_type ctx i with _ -> raise (TypeError (ctx, UnboundVar i)))
    | Const v -> (try Context.get_const_type ctx v with _ -> raise (TypeError (ctx, UnboundConst v)))
    | Type l -> Type (Univ.shift 1 l)
    | Fun (v, t, body) -> Pi (v, t, aux (Context.push_var ctx (v, t, None)) body)
    | Pi (v, t, body) ->
      let t = whd_all ctx t in
      let i = match aux ctx t with | Type i -> i | _ -> raise (TypeError (ctx, NotAType t)) in
      let ctx = Context.push_var ctx (v, t, None) in
      let body = whd_all ctx body in
      let j = match aux ctx body with | Type i -> i | _ -> raise (TypeError (ctx, NotAType body)) in
      Type (Univ.max i j)
    | App (f :: a) ->
      List.fold_left (fun ty t ->
        match whd_all ctx ty with
        | Pi (_, ty, body) ->
          if unify ctx (aux ctx t) ty then beta ctx t body else raise (TypeError (ctx, TypeMismatch (ty, t)))
        | _ -> raise (TypeError (ctx, IllegalApplication (App (f :: a))))) (aux ctx f) a
    | Let (v, ty, t, body) -> beta ctx ty (aux (Context.push_var ctx (v, ty, Some t)) body)
    | _ -> raise (TypeError (ctx, IllFormed t))
  in aux ctx t

let print_type_error ?(debug=false) ctx e =
  let print = if debug then debug_print else print ctx in
  match e with
  | UnboundVar i -> print_string "Unbound variable "; print_int i; print_string "\n"
  | UnboundConst v -> print_string "Unbound constant "; print_string v ; print_string "\n"
  | NotAType t -> print t; print_string " has type "; print (type_of ctx t); print_string ", it is not a type"; print_string "\n"
  | IllegalApplication t -> print_string "Illegal application in "; print t; print_string "\n"
  | TypeMismatch (ty, t) ->
    let tyt = try type_of ctx t with e -> if debug then Const "???" else raise e in
    print_string "Term "; print t; print_string " has type "; print tyt; print_string " while it is expected to have type "; print ty; print_string "\n"
  | IllFormed t -> print t; print_string " is ill-formed"; print_string "\n"
  | NoBody t -> print t; print_string "has no body"; print_string "\n"

