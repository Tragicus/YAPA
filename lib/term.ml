open Utils

type 'a telescope = (string * 'a) list
type 'a arity = 'a telescope * 'a


type t =
  | Var of int (* De Bruijn indices *)
  | Const of string
  | Fun of t telescope * t
  | App of t list (* FIXME: slow *)
  | Type of Univ.t
  | Pi of t telescope * t
  | Let of string * t * t * t
  | Ind of (* arity *) t * (* constructors *) t list
  | Construct of t * int
  | Case of (* inductive *) t * (* recursive *) bool

(* Invariant : depth = List.length var *)
type context = {
  depth : int;
  var : (string option * t * t option) list;
  const : (t * t) SMap.t
}

type type_error =
  | UnboundVar of int
  | UnboundConst of string
  | NotAType of t
  | IllegalApplication of t
  | TypeMismatch of t * t
  | IllFormed of t
  | NoBody of t
  | NotGround of t
  | IllegalConstructorReturnType of t
  | NonPositive of t
  | PropElimination of t

exception TypeError of context * type_error

let head = function
  | App (f :: _) -> f
  | t -> t

let destVar = function
  | Var v -> v
  | _ -> raise Not_found

let destConst = function
  | Const c -> c
  | _ -> raise Not_found

let destFun = function
  | Fun (tele, body) -> (tele, body)
  | t -> ([], t)

let destApp = function
  | App (f :: args) -> f, args
  | f -> f, []

let destType = function
  | Type s -> s
  | _ -> raise Not_found

let destPi = function
  | Pi (tele, body) -> (tele, body)
  | t -> ([], t)

let destLet = function
  | Let (v, ty, t, body) -> (v, ty, t, body)
  | _ -> raise Not_found

let destInd = function
  | Ind (a, c) -> (a, c)
  | _ -> raise Not_found

let destConstruct = function
  | Construct (ind, i) -> (ind, i)
  | _ -> raise Not_found

let destCase = function
  | Case (ind, r) -> (ind, r)
  | _ -> raise Not_found

let mkApp f args =
  if args = [] then f else
  let f, fargs = destApp f in
  App (f :: fargs @ args)

let mkFun f body =
  if f = [] then body else
  match body with
  | Fun (tele, body) -> Fun (f @ tele, body)
  | _ -> Fun (f, body)

let mkPi f body =
  if f = [] then body else
  match body with
  | Pi (tele, body) -> Pi (f @ tele, body)
  | _ -> Pi (f, body)

let rec print e =
  let (+) = fun _ e -> print e in
  let ( ++ ) = fun _ s -> print_string s in
  let pr_telescope =
    List.iter (fun (c, t) -> () ++ " (" ++ c ++ " : " + t ++ ")") in
  match e with
  | Fun (tele, body) -> () ++ "(fun "; pr_telescope tele ++ " => " + body ++ ")"
  | Pi (tele, body) -> () ++ "(forall "; pr_telescope tele ++ ", " + body ++ ")"
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
  | Ind (arity, constructors) ->
    () ++ "ind" ++ " : " + arity ++ " :="; List.iter (fun t -> () ++ " | " + t) constructors
  | Construct (ind, id) ->
    () ++ "ind.mk(" + ind ++ ")."; print_int id
  | Case (ind, recursive) ->
    () ++ (if recursive then "ind.fix(" else "ind.case(") + ind ++ ")"
  | _ -> raise (TypeError ({ depth = 0; var = []; const = SMap.empty }, IllFormed e))

(* Replaces t by \lambda^k. t, avoiding capture *)
let rec bump k t = if k = 0 then t else subst (fun i -> Var (i + k)) t

(* Replaces every `Var i` in `t` by `f i`, avoiding capture. *)
and subst f t =
  let rec aux k t =
    match t with
    | Var i when i < k -> t
    | Const _ | Type _ -> t
    | Var i -> bump k (f (i - k))
    | App l -> App (List.map (aux k) l)
    | Fun (tele, body) ->
      let k, tele = List.fold_left_map (fun k (v, ty) -> k+1, (v, aux k ty)) k tele in
      Fun (tele, aux k body)
    | Pi (tele, body) ->
      let k, tele = List.fold_left_map (fun k (v, ty) -> k+1, (v, aux k ty)) k tele in
      Pi (tele, aux k body)
    | Let (v, ty, t, body) -> Let (v, aux k ty, aux k t, aux (k+1) body)
    | Ind (arity, constructors) ->
      Ind (aux k arity, List.map (aux (k+1)) constructors)
    | Construct (ind, id) -> Construct (aux k ind, id)
    | Case (ind, r) -> Case (aux k ind, r) in
  aux 0 t

(* [beta t t'] beta-reduces (\lambda. t') t *)
let beta t = subst (fun i -> if i = 0 then t else Var (i-1))

let is_ground t = try ignore (subst (fun _ -> raise Not_found) t); true with Not_found -> false

module Context = struct
  type t = context

  let empty = { depth = 0; var = []; const = SMap.empty }

  let depth ctx = ctx.depth

  let find_var ctx i =
    try List.nth ctx.var i with _ -> raise (TypeError (ctx, UnboundVar i))

  let find_const ctx c =
    try SMap.find c ctx.const with _ -> raise (TypeError (ctx, UnboundConst c))

  let get_var_name ctx i =
    let (v, _, _) = find_var ctx i in
    Option.value v ~default:("_" ^ string_of_int i)
  let get_var_type ctx i = let (_, ty, _) = find_var ctx i in bump i ty
  let get_var_body ctx i =
    let (_, _, t) = find_var ctx i in
    match t with
    | None -> raise (TypeError (ctx, NoBody (Var i)))
    | Some body -> bump i body

  let var_depth ctx = ctx.depth

  let get_const_type ctx c = fst (find_const ctx c)
  let get_const_body ctx c = snd (find_const ctx c)

  let push_var (v, ty, body) ctx = { ctx with depth = ctx.depth+1; var = (v, bump 1 ty, Option.map (bump 1) body) :: ctx.var }

  let push_const c (t, ty) ctx = { ctx with const = SMap.add c (subst (fun _ -> raise (TypeError (ctx, NotGround t))) t, ty) ctx.const }

  let push_telescope tele ctx =
    List.fold_left (fun ctx (v, ty) -> push_var (Some v, ty, None) ctx) ctx tele

  (* Unused?
  let pop_var ctx =
    match ctx.var with
    | [] -> ctx (* TOTHINK: should I fail? *)
    | _ :: var -> { ctx with depth = ctx.depth-1; var }
  *)

  let print ctx =
    print_string "CTX:\n\t Local variables:\n";
    List.iteri (fun i (v, ty, t) -> print_string "\t\t"; print_string (Option.value v ~default:("_" ^ string_of_int i)); print_string " : "; print ty; (match t with | None -> () | Some t -> print_string " := "; print t); print_string "\n") ctx.var;
    print_string "\n\t Global variables:\n";
    SMap.iter (fun v (ty, body) -> print_string "\t\t"; print_string v; print_string " : "; print ty; print_string " := "; print body; print_string "\n") ctx.const;
    print_string "\n"
end

let occurs t t' =
  let rec aux t t' =
    if t = t' then raise Not_found else
    match t' with
    | Var _ | Type _ | Const _ -> ()
    | App l -> List.iter (aux t) l
    | Fun (tele, body) | Pi (tele, body) -> 
      List.iter (fun (_, ty) -> aux t ty) tele; aux (bump 1 t) body
    | Let (_, ty, t', body) ->
      aux t ty; aux t t'; aux (bump 1 t) body
    | Ind (arity, constructors) ->
      aux t arity; List.iter (aux (bump 1 t)) constructors
    | Construct (ind, _) -> aux t ind
    | Case (ind, _) -> aux t ind
  in try aux t t'; false with Not_found -> true

type whd_flags = {
  beta    : bool;
  delta   : bool;
  eta     : bool;
  iota    : bool;
  zeta    : bool;
  iota_all: bool;
  once    : bool;
}
  
let whd_flags_none = {
  beta     = false;
  delta    = false;
  eta      = false;
  iota     = false;
  zeta     = false;
  iota_all = false;
  once     = false;
}

let whd_flags_all = {
  beta     = true;
  delta    = true;
  eta      = true;
  iota     = true;
  zeta     = true;
  iota_all = true;
  once     = false;
}

(* [eta t] eta-reduces `t`, i.e. turns `Fun [(_, _)] (App (x :: l @ [Var 0]))` into `App (x :: l)` *)
let eta t =
  match t with
  | Fun ([(_, _)], App l) -> 
    (match List.rev l with
    | Var 0 :: (_ :: _ as l) when not (occurs (Var 0) (App l)) ->
      (match List.rev l with
      | [t] -> t
      | l -> App l)
    | _ -> t)
  | _ -> t

(* [iota ctx t] iota-reduces `t`, i.e. turns `App (Case (App (ind :: indargs), r) :: ret :: branches @ [App (Construct (ind, i) :: sargs)]` into:
  - `App (List.nth branches i :: indargs @ sargs` if `r` is `false` (non-recursive match)
  - `App (List.nth branches i :: indargs @ sargs @ rargs` with `args` being recursive calls on the elements of `sargs` that are from the inductive type being matched against if `r` is `true` (recursive match) *)

let rec iota ?(flags=whd_flags_all) ctx t =
  let h, args = destApp t in
  match destCase h with
  | exception Not_found -> t
  | ind, recursive ->
  let ind, aargs = destApp (whd ctx ind) in
  let (a, c) = try destInd ind with Not_found -> raise (TypeError (ctx, IllFormed h)) in
  let nc = List.length c in
  (* Getting the subject. *)
  (match Utils.split_list_at (1 + nc) args with
  | exception Not_found | _, [] -> t
  | objs, subject :: eargs ->
  let ci, sargs = destApp (whd ~flags:(if flags.iota_all then whd_flags_all else flags) ctx subject) in
  (match destConstruct ci with
  | exception Not_found -> t
  | _, i ->
  let rargs =
    if not recursive then [] else
    let ctx = Context.push_var (None, a, None) ctx in
    let ctele, _ = destArity ctx (List.nth c i) in
    let _, _, rargs = List.fold_left (fun (iarg, ctx, rargs) (n, arg) ->
      iarg+1,
      Context.push_var (Some n, arg, None) ctx,
      let hd, args = destApp (whd ctx arg) in
      match hd with
      | Var i when i = iarg ->
        let args = List.map
          (subst (fun i ->
            if i < iarg then List.nth sargs (iarg-1-i) else
            if i = iarg then ind else Var(i)))
          args in
        (mkApp (Case (mkApp ind args, recursive)) (objs @ [List.nth sargs iarg])) :: rargs
      | _ -> rargs) (0, ctx, []) ctele in
    List.rev rargs in
  let targs = aargs @ sargs @ rargs @ eargs in
  mkApp (List.nth objs (1+i)) targs))

and whd ?(flags=whd_flags_all) ctx t =
  match t with
  | Const c when flags.delta ->
    let t = Context.get_const_body ctx c in
    if flags.once then t else whd ~flags ctx t
  | Fun ([(_, _)], _) as t when flags.eta -> eta t
  | Fun ((v, ty) :: tele, body) when flags.eta ->
    let body = whd ~flags:{ whd_flags_none with eta = true; once = flags.once } (Context.push_var (Some v, ty, None) ctx) (mkFun tele body) in
    let t = mkFun [(v, t)] body in
    if flags.once then t else eta t
  | Let (_, _, t, body) when flags.zeta -> whd ~flags ctx (beta t body)
  | App (f :: args) ->
    (match destApp (mkApp (whd ~flags ctx f) args) with
    | Fun (_ :: tele, body), x :: args when flags.beta ->
      let t = mkApp (beta x (mkFun tele body)) args in
      if flags.once then t else whd ~flags ctx t
    | Case (_, _), _ when flags.iota ->
      let t' = iota ~flags ctx t in
      if flags.once || t' = t then t else whd ~flags ctx t'
    | h, _ -> mkApp h args)
  | t -> t

and destArity ?(whd_rty=false) ctx t =
  match whd ctx t with
  | Pi (tele, body) ->
    let tele2, r = destArity (Context.push_telescope tele ctx) body in
    tele @ tele2, r
  | t' -> [], if whd_rty then t' else t

(* Complete reduction. *)
let rec eval ctx t =
  match t with
  | Const c ->
    (match Context.get_const_body ctx c with
    | exception Not_found -> t
    | t -> eval ctx t)
  | Fun ([(_, _)], _) as t -> eta t
  | Fun ((v, ty) :: tele, body) ->
    let body = eval (Context.push_var (Some v, ty, None) ctx) (mkFun tele body) in
    eta (mkFun [(v, t)] body)
  | Let (_, _, t, body) -> eval ctx (beta t body)
  | App l ->
    (match List.map (eval ctx) l with
    | Fun (_ :: tele, body) :: x :: args ->
      let t = mkApp (beta x (mkFun tele body)) args in
      eval ctx t
    | Case (_, _) :: _ ->
      let t' = iota ctx t in
      if t' = t then t else eval ctx t'
    | l -> App l)
  | t -> t

let reducible ctx t =
  let h, args = destApp t in
  match h with
  | Type _ | Pi _ | Ind _ | Construct _ -> false
  | Fun _ -> args <> []
  | Case (ind, _) ->
    let ind, _ = destApp (whd ctx ind) in
    let (_, c) = try destInd ind with Not_found -> raise (TypeError (ctx, IllFormed ind)) in
    let nc = List.length c in
    if List.length args <= 1 + nc then false else
    (match destApp (whd ctx (List.nth args (1 + nc))) with
    | Construct _, _ -> true
    | _, _ -> false)
  | Var i -> (try let _ = Context.get_var_body ctx i in true with TypeError (_, NoBody _) -> false)
  | Const _ | Let _ -> true
  | _ -> failwith "Internal error : head should not by an application."

let rec unify ctx t1 t2 =
  let unify_telescope ctx tele1 tele2 =
    if List.length tele1 <> List.length tele2 then ctx, false else
    let ctx = ref ctx in
    let b = 
      List.for_all2 (fun (v, ty1) (_, ty2) ->
        let b = unify !ctx ty1 ty2 in
        ctx := Context.push_var (Some v, ty1, None) !ctx;
        b) tele1 tele2 in
    !ctx, b in
  let unify_fun ?(builder=mkFun) ctx (tele1, body1) (tele2, body2) =
    let l1 = List.length tele1 in
    let l2 = List.length tele2 in
    let l = min l1 l2 in
    let tele1, etele1 = Utils.split_list_at l tele1 in
    let tele2, etele2 = Utils.split_list_at l tele2 in
    let ctx', b = unify_telescope ctx tele1 tele2 in
    b && unify ctx' (builder etele1 body1) (builder etele2 body2) in
  (* unifies t1 and t2 when t2 is reducible *)
  let rec mixed ctx (h1, args1 as t1) (h2, args2) =
    match h1, h2 with
    | h1, Fun (tele2, body2) ->
      (match h1 with
      | Fun (tele1, body1) ->
        unify_fun ctx (tele1, body1) (tele2, body2) && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (destApp (whd ~flags:{ whd_flags_none with beta = true; once = true } ctx (mkApp h2 args2)))
    | h1, Let (_, ty2, t2, body2) ->
      (match h1 with
      | Let (v, ty1, t1, body1) -> unify ctx ty1 ty2 && unify ctx t1 t2 && unify (Context.push_var (Some v, ty1, None) ctx) body1 body2 && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (destApp (whd ~flags:{ whd_flags_none with zeta = true; once = true } ctx (mkApp h2 args2)))
    | h1, Var i2 ->
      (match h1 with
      | Var i1 -> i1 = i2 && List.for_all2 (unify ctx) args1 args2
      | _ -> false) ||
      aux ctx t1 (destApp (mkApp (Context.get_var_body ctx i2) args2))
    | _, Const c -> aux ctx t1 (destApp (mkApp (Context.get_const_body ctx c) args2))
    | h1, Case (ind2, recursive2) ->
      (match h1 with
      | Case (ind1, recursive1) -> recursive1 = recursive2 && unify ctx ind1 ind2
      | _ -> false) ||
      aux ctx t1 (destApp (whd ~flags:{ whd_flags_none with iota = true; once = true } ctx (mkApp h2 args2)))
    | _, _ -> failwith "Internal error : non-reducible term classified as maybe reducible."
  and aux ctx (h1, args1 as t1) (h2, args2 as t2) =
    if reducible ctx (mkApp h2 args2) then mixed ctx t1 t2 else
    if reducible ctx (mkApp h1 args1) then mixed ctx t2 t1 else
    match h1, h2 with
    | Var i, Var j -> i = j && List.for_all2 (unify ctx) args1 args2
    | Type _, Type _ -> true (* FIXME: implement universes *)
    | Fun (tele1, body1), Fun (tele2, body2)
    | Pi (tele1, body1), Pi (tele2, body2) ->
      unify_fun ~builder:mkPi ctx (tele1, body1) (tele2, body2) && List.for_all2 (unify ctx) args1 args2
    | Ind (a1, c1), Ind (a2, c2) -> unify ctx a1 a2 &&
      let ctx = Context.push_var (None, a1, None) ctx in
      List.for_all2 (unify ctx) c1 c2
    | Construct (ind1, i1), Construct (ind2, i2) -> i1 = i2 && unify ctx ind1 ind2
    | Case (ind1, r1), Case (ind2, r2) -> r1 = r2 && unify ctx ind1 ind2
    | _, _ -> false in
  aux ctx (destApp t1) (destApp t2)

let rec type_of ctx t =
  let type_telescope ?(get_sorts=false) ctx tele =
    List.fold_left_map (fun ctx (v, t) -> 
      let ty = type_of ctx t in
      match whd ctx ty with
      | Type s ->
        let ty = if get_sorts then Type s else ty in
        Context.push_var (Some v, t, None) ctx, (v, ty)
      | _ -> raise (TypeError (ctx, NotAType t))) ctx tele in
  match t with
  | Var i -> (try Context.get_var_type ctx i with _ -> raise (TypeError (ctx, UnboundVar i)))
  | Const v -> (try Context.get_const_type ctx v with _ -> raise (TypeError (ctx, UnboundConst v)))
  | Type l -> Type (Univ.shift 1 l)
  | Fun (tele, body) ->
    let ctx, _ = type_telescope ctx tele in
    mkPi tele (type_of ctx body)
  | Pi (tele, body) ->
    let ctx, tytele = type_telescope ctx tele in
    let sorts = List.map destType (List.map snd tytele) in
    let j =
      try destType (whd ctx (type_of ctx body)) with
      | Not_found -> raise (TypeError (ctx, NotAType body))  in
    (* TOTHINK: Do I really need to reverse the sorts list? *)
    Type (List.fold_left (fun j i -> Univ.max i j) j (List.rev sorts))
  | App (f :: a) ->
    List.fold_left (fun ty t ->
      match whd ctx ty with
      | Pi ([], body) -> body
      | Pi ((_, ty) :: tele, body) ->
        if unify ctx (type_of ctx t) ty then beta t (mkPi tele body) else raise (TypeError (ctx, TypeMismatch (ty, t)))
      | _ -> raise (TypeError (ctx, IllegalApplication (App (f :: a))))) (type_of ctx f) a
  | Let (v, ty, t, body) -> beta ty (type_of (Context.push_var (Some v, ty, Some t) ctx) body)
  | Ind (a, c) ->
    (* Check the arity *)
    let _ = match whd ctx (type_of ctx a) with
      | Type _ -> ()
      | _ -> raise (TypeError (ctx, NotAType a)) in
    (* Make the type of the inductive and push it on the context *)
    let ctx = Context.push_var (None, a, None) ctx in
    (* [check_positivity ctx c] ensures that `c` contains only positive occurrences of the inductive being defined.
       returns true when the return type is the inductive type
       raises `Not_found` when there is a non positive occurrence *)
    (* strict = 
       0 : no occurence
       1 : strictly positive occurences
       2 : positive occurences *)
    let rec check_positivity ?(strict=2) ?(depth=0) ctx t =
      match whd ctx t with
      | Var i -> if i = depth && strict = 0 then raise Not_found else true
      | App ((Var i) :: args) when i = depth ->
        if strict = 0 then raise Not_found else
        let () = List.iter (fun t -> ignore (check_positivity ~strict:0 ~depth ctx t)) args in
        true
      | Pi (tele, body) ->
        let strict' = if strict = 0 then 0 else strict-1 in
        let ctx, depth = List.fold_left (fun (ctx, depth) (n, t) ->
          let _ = check_positivity ~strict:strict' ~depth ctx t in
          Context.push_var (Some n, t, None) ctx, depth+1) (ctx, depth) tele in
        check_positivity ~strict ~depth:depth ctx body
      | t -> if occurs (Var depth) t then raise Not_found else false in
    let () = List.iter (fun c ->
      match type_of ctx c with
      | Type _ ->
        let b = try check_positivity ctx c with Not_found -> raise (TypeError (ctx, NonPositive c)) in
        if not b then raise (TypeError (ctx, IllegalConstructorReturnType c))
      | _ -> raise (TypeError (ctx, NotAType c))) c in
    a
  | Construct (ind, i) ->
    let _ = type_of ctx ind in
    let _, c = try destInd (whd ctx ind) with _ -> raise (TypeError (ctx, IllFormed t)) in
    if List.length c <= i then raise (TypeError (ctx, IllFormed t)) else
    beta ind (List.nth c i)
  | Case (ind, recursive) ->
    (* Check ind is well-typed *)
    let _ = type_of ctx ind in
    (* Get ind's content *)
    let ind, _ = destApp (whd ctx ind) in
    let (a, c) = try destInd ind with _ -> raise (TypeError (ctx, IllFormed t)) in
    (* Get a's arity *)
    let atele, _ = destArity ctx a in
    let na = List.length atele in
    (* FIXME : The return type's return type should not necessarily be Prop. *)
    (* Build the predicate that gives the return type of the match... *)
    let rty = mkPi (atele @ [("_", mkApp ind (List.init na (fun i -> Var (na-i-1))))]) (Type (Univ.static 0)) in
    (* Start building the result's telescope, in reverse order *)
    let revtele = [("_", rty)] in
    (* The constructors expect the inductive type to be at position 0 in the context. *)
    let ctx = Context.push_var (None, a, None) ctx in
    (* Transform the constructors into match branches and push them on the telscope
     ic : number of constructors already seen, every DeBruijn index should be bumped by ic before being pushed on the telescope.*)
    let nc, revtele = List.fold_left (fun (ic, revtele) c ->
      let ctele, cret = destArity ~whd_rty:true ctx c in
      let nc = List.length ctele in
      (* Get the recursive calls telescope (if applicable) *)
      let rec_calls =
        if not recursive then [] else
        let _, _, rec_calls = List.fold_left (fun (iarg, ctx, rec_calls) (n, arg) ->
          iarg+1,
          Context.push_var (Some n, arg, None) ctx,
          let hd, args = destApp (whd ctx arg) in
          match hd with
          | Var i when i = iarg ->
            let args = List.map (bump (nc-iarg)) args in
            let args = args @ [Var (nc-iarg-1)] in
            ("_", (mkApp (Var nc) args)) :: rec_calls
          | _ -> rec_calls) (0, ctx, []) ctele in
        List.rev rec_calls in
      (* We need to bump because there is the predicate between the arguments the constructors might refer to and the constructors themselves. *)
      let ctele, cret = destPi (bump 1 (beta ind (mkPi ctele cret))) in
      let ctele = ctele @ rec_calls in
      let _, cargs = destApp cret in
      let arg = mkPi ctele (bump (List.length rec_calls) (mkApp (Var nc) (cargs @ [mkApp (Construct (cret, ic)) (List.init nc (fun i -> Var (nc-1-i)))]))) in
      let arg = bump ic arg in
      (ic+1, ("_", arg) :: revtele)) (0, revtele) c in
    let revtele = ("_", mkApp (bump (na+nc+1) ind) (List.init na (fun i -> Var (na-i-1)))) :: revtele in
    let tele = List.rev revtele in
    mkPi tele (mkApp (Var (na+nc+1)) (List.init (na+1) (fun i -> Var (na-i))))

  | _ -> raise (TypeError (ctx, IllFormed t))

