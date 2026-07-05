open Utils
module E = Engine.Term
module EC = E.Context

type univ = int SMap.t

type 'a binder = string * 'a * 'a option * bool (* implicit *)
type 'a telescope = 'a binder list
type 'a arity = 'a telescope * 'a

(* We do not follow the convention from the kernel and the engine because we want to clear implicits on an arbitrary term, e.g. as in `@(f x) y`. *)
type 'a head =
  | Const of string * (string list * univ list) option
  | Fun of bool (* true if forall *) * 'a telescope * 'a
  | Type of string * univ
  | Ind of (* name *) string * (* arity *) 'a * (* constructors *) 'a list
  | Construct of 'a * int
  | Case of (* recursive *) bool *
            (* subject *) 'a *
            (* inductive *) 'a option *
            (* return type *) 'a * 
            (* branches *) ('a * 'a) list
  | Evar of string
  | App of term list

and term = { hd: term head; implicits: bool }
type t = term

let of_hd hd = { hd; implicits = true }
let clear_implicits t = { t with implicits = false }
let mkConst c su = of_hd (Const (c, su))
let mkVar v = mkConst v None
let mkForallOrFun forall tele t =
  if List.is_empty tele then t else
  clear_implicits (of_hd (match t.hd with
    | Fun (forall', tele', body) when forall' = forall ->
      Fun (forall, tele @ tele', body)
    | _ -> Fun (forall, tele, t)))
let mkForall = mkForallOrFun true
let mkFun = mkForallOrFun false
let mkLet ?(forall=false) x ty t = mkForallOrFun forall [(x, ty, Some t, false)]
let mkType s u = of_hd (Type (s, u))
let mkInd v a c = of_hd (Ind (v, a, c))
let mkConstruct t i = of_hd (Construct (t, i))
let mkCase r s ind ty b = of_hd (Case (r, s, ind, ty, b))
let mkApp args t = if args = [] then t else { hd = App (t :: args); implicits = true }

let destVar t =
  match t.hd with
  | Const (v, None) -> v
  | _ -> raise Not_found

let destConst t =
  match t.hd with
  | Const (c, su) -> (c, su)
  | _ -> raise Not_found

let destFun t =
  let rec extract tele = function
    | ((_, _, None, _) as b) :: rest -> extract (b :: tele) rest
    | rest -> List.rev tele, rest in
  match t.hd with
  | Fun (false, tele, body) ->
      let tele, rest = extract [] tele in
      (tele, mkFun rest body)
  | _ -> ([], t)

let destType t =
  match t.hd with
  | Type (s, u) -> (s, u)
  | _ -> raise Not_found

let destForall t =
  match t.hd with
  | Fun (true, ((_, _, None, _) as b) :: tele, body) ->
      (b, mkForall tele body)
  | _ -> raise Not_found

let destLet t =
  match t.hd with
  | Fun (forall, ((x, ty, Some t, _) :: tele), body) -> (x, ty, t, mkForallOrFun forall tele body)
  | _ -> raise Not_found

let destInd t =
  match t.hd with
  | Ind (v, a, c) -> (v, a, c)
  | _ -> raise Not_found

let destConstruct t =
  match t.hd with
  | Construct (ind, i) -> (ind, i)
  | _ -> raise Not_found

let destCase t =
  match t.hd with
  | Case (r, s, ind, ty, b) -> (r, s, ind, ty, b)
  | _ -> raise Not_found

let destEvar t =
  match t.hd with
  | Evar i -> i
  | _ -> raise Not_found

let destApp t = 
  match t.hd with
  | App (t :: args) -> (t, args)
  | _ -> raise Not_found

let safe_dest_app t =
  match t.hd with
  | App (t :: args) -> (t, args)
  | _ -> (t, [])

module Context = struct
  type t = {
    var: int list SMap.t;
    sort: Kernel.Univ.Sort.t SMap.t;
    univ: Kernel.Univ.Level.t SMap.t;
    evar: int SMap.t;
    ctx: E.Context.t
  }

  (* TOTHINK: Should I translate more things? *)
  let of_engine ctx = { var = IMap.fold (fun i (v, _, _, _) -> SMap.update v (fun l -> Some (i :: Option.value ~default:[] l))) ctx.E.var SMap.empty; sort = SMap.empty; univ = SMap.empty; evar = SMap.empty; ctx }
  let empty = of_engine EC.empty

  let push_var ?(avoid_capture=true) (v, ty, body, impl) ctx =
    let d = IMap.cardinal ctx.ctx.E.var in
    let ectx, _ = EC.push_var ~avoid_capture (v, ty, body, impl) ctx.ctx in
    { ctx with var = SMap.update v (fun l -> Some (d :: Option.value ~default:[] l)) ctx.var; ctx = ectx }, ()

  let pop_var ctx =
    let d = EC.depth ctx.ctx in
    let v = EC.get_var_name (d - 1) ctx.ctx in
    let ectx, _ = EC.pop_var ctx.ctx in
    { ctx with var = SMap.update v (function | None | Some [] -> failwith "unreachable" | Some [_] -> None | Some (_ :: l) -> Some l) ctx.var; ctx = ectx }, ()


  module Monad = struct
    include Utils.ContextMonad(struct type u = t type t = u end)

    let to_engine f ctx =
      let ctx, r = f (of_engine ctx) in
      ctx.ctx, r

    let of_engine f ctx =
      let ectx, r = f ctx.ctx in
      { ctx with ctx = ectx }, r
  end

  open Monad.Notations

  let with_var ?(avoid_capture=true) v f ctx =
    let ctx', () = push_var ~avoid_capture v ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var; ctx = { ctx'.ctx with var = ctx.ctx.var } }, r)

  let with_telescope ?(avoid_capture=true) tele f ctx =
    let ctx', () = Monad.List.fold_left (fun b () -> push_var ~avoid_capture b) tele () ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var; ctx = { ctx'.ctx with var = ctx.ctx.var } }, r)

  let fold_telescope ?(avoid_capture=true) f x tele k ctx =
    let ctx', r = Monad.List.fold_left (fun b x ->
      let* r = f x b in
      let+ () = push_var ~avoid_capture b in
      r) tele x ctx in
    let ctx', r = k r ctx' in
    ({ ctx' with var = ctx.var }, r)
end

open Context.Monad.Notations

let print_univ l = 
  let (+) = String.cat in
  let print_atom (v, n) = v + (if n = 0 then "" else " + " + string_of_int n) in
  match List.map print_atom (SMap.to_list l) with
  | [] -> failwith "Anomaly: empty universe level"
  | [s] -> s
  | s :: l -> "max(" + String.concat ", " (s :: l) + ")"

let print t =
  let (+) = String.cat in
  let rec aux t = 
    match t.hd with
    | Const (c, su) -> c + (match su with | None -> "" | Some (s, u) -> "@{" + String.concat ", " s + "; " + String.concat ", " (List.map print_univ u)), true
    | Type (s, u) -> (if (s = "_" || s = "Type" || s = "Prop" || s = "SProp") && SMap.mem "_" u && SMap.find "_" u = 0
      then match s with | "_" -> "Type" | _ -> s
      else "Type@{" + s + "; " + print_univ u), true
    | Fun (f, tele, t) -> ((if f then "forall " else "fun ") + String.concat " " (List.map (fun (v, ty, t, impl) -> (if impl then "{" else "(") + v + " : " + fst (aux ty) + (match t with | None -> "" | Some t -> " := " + fst (aux t)) + (if impl then "}" else ")")) tele) + (if f then ", " else " => ") + fst (aux t)), false
    | Ind (v, a, c) -> "ind " + v +  " : " + fst (aux a) + " :=" + " | " + String.concat " | " (List.map (fun t -> fst (aux t)) c), false
    | Construct (ind, id) -> "ind.mk(" + fst (aux ind) + ")." + string_of_int id, true
    | Case (r, s, ind, ty, b) -> "match " + (if r then "rec " else "") + fst (aux s) + (match ind with | None -> " " | Some ind -> " as " + fst (aux ind)) + " return " + fst (aux ty) + " with " + String.concat " " (List.map (fun (l, r) -> "| " + fst (aux l) + " => " + fst (aux r)) b), false
    | Evar v -> (if v = "_" then "?" else ("?" + v)), true
    | App _ -> let (t, args) = destApp t in fst (aux t) + " " + String.concat " " (List.map (fun (t, atomic) -> if atomic then t else "(" + t + ")") (List.map aux args)), false in
  let s, atom = aux t in
  if t.implicits then s else
  "@" + if atom then s else "(" + s + ")"

type error =
  | UnboundSort of string
  | UnboundUniv of string
  | IllegalUniverse of univ
  | WrongPolymorphism of t
  | UnknownInductive of t
  | IllegalBranch of (t * t)
  | DuplicateBranch of int
  | MissingBranch of int

exception Error of Context.t * error

let rec elaborate ?(evars_with_ctx=true) (t : t) =
  let ret = Context.Monad.ret in
  let sort = function
    | "Type" -> ret Kernel.Univ.Sort.Type
    | "Prop" -> ret Kernel.Univ.Sort.Prop
    | "SProp" -> ret Kernel.Univ.Sort.SProp
    | "_" -> Context.Monad.of_engine (EC.new_sort None)
    | s -> fun ctx -> try ctx, SMap.find s ctx.sort with _ -> raise (Error (ctx, UnboundSort s)) in
  let univ u ctx =
    if SMap.mem "_" u then
      if SMap.cardinal u <> 1 then raise (Error (ctx, (IllegalUniverse u))) else
      Context.Monad.of_engine (EC.new_level None) ctx
    else
      let ctx, u = Context.Monad.List.map (fun (u, i) ctx -> ctx, try Kernel.Univ.Level.add i (SMap.find u ctx.univ) with _ -> raise (Error (ctx, UnboundUniv u))) (SMap.to_list u) ctx in
      ctx, List.fold_left Kernel.Univ.Level.max Kernel.Univ.Level.base u in
  let hd, args = safe_dest_app t in
  let impl = hd.implicits in
  let* hd = match hd.hd with
    | Type (s, u) -> let* s = sort s in let+ u = univ u in E.of_hd (E.Type (s, u))
    | Const (c, su) ->
      let** v = fun ctx -> SMap.find_opt c ctx.Context.var in
      (match v with
      | Some (v :: _) ->
        if su <> None then fun ctx -> raise (Error (ctx, WrongPolymorphism (mkConst c su))) else
        let** d = fun ctx -> EC.depth ctx.Context.ctx in
        Context.Monad.ret (E.of_hd (E.Var (d - 1 - v)))
      | _ ->
        let* cuniv = Context.Monad.of_engine (EC.Monad.to_mut (EC.get_const_univ c)) in
        let (s, u) = Option.value ~default:(List.init (IMap.cardinal cuniv.sorts) (fun _ -> "_"), List.init (IMap.cardinal cuniv.levels - 1) (fun _ -> SMap.singleton "_" 0)) su in
        let* () = if List.length s <> IMap.cardinal cuniv.sorts || List.length u + 1 <> IMap.cardinal cuniv.levels then fun ctx -> raise (Error (ctx, WrongPolymorphism (mkConst c su))) else Context.Monad.ret () in
        let* s' = Context.Monad.List.map sort s in
        let+ u' = Context.Monad.List.map univ u in
        E.of_hd (E.Const (c, s', u')))
    | Fun (f, tele, body) -> fun ctx ->
      let rec telescope rtele = function
        | [] -> let+ body = elaborate ~evars_with_ctx body in rtele, body 
        | (v, ty, t, impl) :: tele ->
          let* ty = elaborate ~evars_with_ctx ty in
          let* t = Context.Monad.Option.map (elaborate ~evars_with_ctx) t in
          let* () = Context.push_var ~avoid_capture:false (v, ty, t, impl) in
          telescope ((v, ty, t, impl) :: rtele) tele in
      let (ctx', (rtele, body)) = telescope [] tele ctx in
      let ctx' = { ctx' with var = ctx.var; ctx = { ctx'.ctx with var = ctx.ctx.var } } in
      ctx', E.of_hd (E.Fun (f, List.rev rtele, body))
    | Ind (v, a, c) ->
      let* a = elaborate ~evars_with_ctx a in
      let+ c = Context.with_var ~avoid_capture:false (v, a, None, false) (Context.Monad.List.map (elaborate ~evars_with_ctx) c) in
      E.of_hd (E.Ind (v, a, c))
    | Construct (ind, i) -> let+ ind = elaborate ~evars_with_ctx ind in E.of_hd (E.Construct (ind, i))
    | Case (r, s, ind, rty, br) ->
      let* s = elaborate ~evars_with_ctx s in
      let* ind' = match ind with | None -> Context.Monad.of_engine (E.typecheck s) | Some ind -> elaborate ~evars_with_ctx ind in
      let* rty = elaborate ~evars_with_ctx rty in
      let* whind = Context.Monad.of_engine (EC.Monad.to_mut (E.whd ind')) in
      let ind = E.of_hd whind.hd in
      let* (_, a, cs) = Context.Monad.of_engine (fun ctx -> try ctx, E.destInd ind with Not_found -> raise (E.TypeError (ctx, E.IllFormed ind'))) in

      let* () = Context.push_var ~avoid_capture:false ("_", a, Some ind, false) in
      let* br = Context.Monad.List.map (fun (c, r) ->
        let (c, cargs) = safe_dest_app c in
        let* chd = elaborate ~evars_with_ctx c in
        let* chd = Context.Monad.of_engine (EC.Monad.to_mut (E.whd chd)) in
        let** (ind', i) = fun ctx -> try E.destConstruct chd with _ -> let () = print_endline ("not a constructor: " ^ E.print chd ctx.Context.ctx) in raise (Error (ctx, IllegalBranch (c, r))) in
        let* b = Context.Monad.of_engine (E.unify (E.bump 1 ind) ind') in
        if not b then fun ctx -> let () = print_endline "wrong inductive" in raise (Error (ctx, IllegalBranch (c, r))) else
        let cty = List.nth cs i in
        let* ctele, _ = Context.Monad.of_engine (E.destArity cty) in
        if List.length (List.filter (fun (_, _, t, impl) -> t = None && not (c.implicits && impl)) ctele) <> List.length cargs then fun ctx ->
          let () = print_endline "wrong number of arguments" in raise (Error (ctx, IllegalBranch (c, r))) else
        let* tele = Context.Monad.List.map (fun (v, (_, ty, t, impl)) ctx ->
          let (v, su) = try destConst v with _ -> let () = print_endline "argument should be a variable" in raise (Error (ctx, IllegalBranch (c, r))) in
          if su <> None then let () = print_endline "argument should not be a constant" in raise (Error (ctx, IllegalBranch (c, r))) else
          ctx, (v, ty, t, impl)) (List.combine cargs ctele) in
        let* _ = Context.Monad.List.fold_left (fun (v, _, _, _) vs ctx -> if SSet.mem v vs then let () = print_endline "variable bound several times" in raise (Error (ctx, IllegalBranch (c, r))) else ctx, SSet.add v vs) tele SSet.empty in
        let* r = Context.with_telescope ~avoid_capture:false tele (elaborate ~evars_with_ctx r) in
        let r = E.beta ind (E.mkFun tele r) in
        Context.Monad.ret (i, r)
      ) br in
      let* () = Context.pop_var in

      let* br = Context.Monad.List.fold_left (fun (i, br) brs ctx -> if IMap.mem i brs then raise (Error (ctx, DuplicateBranch i)) else ctx, IMap.add i br brs) br IMap.empty in
      let+ br = fun ctx -> ctx, List.mapi (fun i (j, br) -> if i <> j then raise (Error (ctx, MissingBranch i)) else br) (IMap.to_list br) in
      E.{hd = E.Case (ind, r); args = rty :: br @ whind.args @ [s] }
    | Evar s ->
        if s = "_" then Context.Monad.of_engine (EC.new_evar ~with_ctx:evars_with_ctx) else
        (fun ctx -> try ctx, E.of_hd (E.Evar (SMap.find s ctx.evar)) with _ ->
          let ctx, t = Context.Monad.of_engine (EC.new_evar ~with_ctx:evars_with_ctx) ctx in
          let i = E.destEvar (E.of_hd t.hd) in
          { ctx with evar = SMap.add s i ctx.evar }, t)
    | App _ -> elaborate ~evars_with_ctx hd in
  let* args = Context.Monad.List.map (elaborate ~evars_with_ctx) args in
  if not impl then Context.Monad.ret (E.mkApp args hd) else
  let* ty = Context.Monad.of_engine (E.typecheck hd) in
  let* tele, ty = Context.Monad.of_engine (E.destArity ~until:(Exact (List.length args)) ~count_implicits:false ~trailing_implicits:false ty) in

  let args' = Dynarray.create () in
  let subst t =
    let n = Dynarray.length args' in
    if n = 0 then t else E.subst (fun i -> if i < n then Dynarray.get args' (n - i - 1) else E.mkVar (i - n)) t in
  (* This is a specialized copy of `Engine.Term.fold_left_args_with_type`, because the arguments do not align with the telescope as the latter assumes. *)

  let rec loop rargs args tele =
    let open EC.Monad.Notations in
    let ret = EC.Monad.ret in
    match tele with | [] -> ret rargs | (_, ty, _, impl) :: tele ->
    let* arg = if impl then EC.new_evar ~ty:(Some (subst ty)) ~with_ctx:evars_with_ctx else ret (List.hd args) in
    let args = if impl then args else List.tl args in
    let () = Dynarray.add_last args' arg in
    loop (arg :: rargs) args tele in
  let* rargs = Context.Monad.of_engine (loop [] args tele) in
  let impl = t.implicits in
  let t = E.mkApp (List.rev rargs) hd in
  if not impl then Context.Monad.ret t else
  let* () = Context.Monad.of_engine (EC.push_telescope ~avoid_capture:false tele) in
  let* tele', _ = Context.Monad.of_engine (E.destArity ~until:(Exact 0) ~count_implicits:false ~trailing_implicits:true ty) in
  let* _ = Context.Monad.of_engine (EC.Monad.List.map (fun _ -> EC.pop_var) (List.init (List.length tele) (fun i -> i))) in
  let+ rargs = Context.Monad.of_engine (loop [] [] tele') in
  E.mkApp (List.rev rargs) t



let print_error e =
  let (+) = String.cat in
  match e with
  | UnboundSort s -> "Unbound sort " + s
  | UnboundUniv u -> "Unbound universe level " + u
  | IllegalUniverse u -> "Illegal universe " + print_univ u
  | WrongPolymorphism t -> "Wrong universe polymorphism " + print t
  | UnknownInductive t -> print t + " is not an inductive type"
  | IllegalBranch (l, r) -> "Illegal match branch " + print l + " => " + print r
  | DuplicateBranch i -> "Duplicate branch for constructor " + string_of_int i
  | MissingBranch i -> "Missing branch for constructor " + string_of_int i
