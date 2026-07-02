open Utils

type 'a binder = string * 'a * 'a option * bool (* implicit *)
type 'a telescope = 'a binder list
type 'a arity = 'a telescope * 'a

type 'a head =
  | Var of int (* De Bruijn indices *)
  | Const of string * Kernel.Univ.Sort.t list * Kernel.Univ.Level.t list
  | Fun of bool (* true if forall *) * 'a telescope * 'a
  | Type of Kernel.Univ.t
  | Ind of string * (* arity *) 'a * (* constructors *) 'a list
  | Construct of 'a * int
  | Case of (* inductive *) 'a * (* recursive *) bool
  | Evar of int

module Head = struct
  type 'a t = 'a head

  let map f hd = match hd with
    | Var v -> Var v
    | Const (v, s, u) -> Const (v, s, u)
    | Fun (x, tele, body) -> Fun (x, List.map (fun (v, ty, t, impl) -> (v, f ty, Option.map f t, impl)) tele, f body)
    | Type u -> Type u
    | Ind (v, a, c) -> Ind (v, f a, List.map f c)
    | Construct (ind, i) -> Construct (f ind, i)
    | Case (ind, i) -> Case (f ind, i)
    | Evar i -> Evar i
end

type term = { hd: term head; args: term list }
type t = term

type context = {
  univ : Kernel.Univ.Context.t;
  var : t binder IMap.t;
  const : (Kernel.Univ.Context.t * Kernel.Term.t * Kernel.Term.t option) SMap.t;
  evar : (t * t option * (t binder IMap.t * t * t) list) IMap.t;
  hints : Kernel.Term.term Pattern.Map.t;
  flags : string SMap.t
}

module CMonad = Utils.ContextMonad(struct type t = context end)
open CMonad.Notations

type type_error =
  | UnboundVar of int
  | UnboundConst of string
  | UnboundEvar of int
  | NotAType of t
  | IllegalApplication of t
  | TypeMismatch of t * t
  | IllFormed of t
  | NoBody of t
  | NotGround of t
  | IllegalConstructorReturnType of t
  | NonPositive of t
  | PropElimination of t
  | HO of t * t
  | OccurCheck of t * t
  | CannotUnify of t * t

exception TypeError of context * type_error

let of_hd hd = { hd; args = [] }
let mkVar v = { hd = Var v; args = [] }
let mkConst c s u = { hd = Const (c, s, u); args = [] }
let mkForallOrFun forall tele t =
  if List.is_empty tele then t else
  { hd = (match t.hd with
    | Fun (forall', tele', body) when forall' = forall && List.is_empty t.args ->
        Fun (forall, tele @ tele', body)
    | _ -> Fun (forall, tele, t));
  args = [] }
let mkForall = mkForallOrFun true
let mkFun = mkForallOrFun false
let mkLet ?(forall=false) x ty t = mkForallOrFun forall [(x, ty, Some t, false)]
let mkType u = { hd = Type u; args = [] }
let mkInd v a c = { hd = Ind (v, a, c); args = [] }
let mkConstruct t i = { hd = Construct (t, i); args = [] }
let mkCase t r = { hd = Case (t, r); args = [] }
let mkEvar i = { hd = Evar i; args = [] }
let mkApp args t = { hd = t.hd; args = t.args @ args }

let destVar t =
  match t.hd with
  | Var v when List.is_empty t.args -> v
  | _ -> raise Not_found

let destConst t =
  match t.hd with
  | Const (c, s, u) when List.is_empty t.args -> (c, s, u)
  | _ -> raise Not_found

let destFun t =
  let rec extract tele = function
    | ((_, _, None, _) as b) :: rest -> extract (b :: tele) rest
    | rest -> List.rev tele, rest in
  match t.hd with
  | Fun (false, tele, body) when List.is_empty t.args ->
      let tele, rest = extract [] tele in
      (tele, mkFun rest body)
  | _ -> ([], t)

let destType t =
  match t.hd with
  | Type s (* Assuming t is well-typed, t.args is empty *) -> s
  | _ -> raise Not_found

let destForall t =
  match t.hd with
  | Fun (true, ((_, _, None, _) as b) :: tele, body) when List.is_empty t.args ->
      (b, mkForall tele body)
  | _ -> raise Not_found

let destLet t =
  match t.hd with
  | Fun (forall, ((x, ty, Some t, _) :: tele), body) when List.is_empty t.args -> (x, ty, t, mkForallOrFun forall tele body)
  | _ -> raise Not_found

let destInd t =
  match t.hd with
  | Ind (v, a, c) when List.is_empty t.args -> (v, a, c)
  | _ -> raise Not_found

let destConstruct t =
  match t.hd with
  | Construct (ind, i) when List.is_empty t.args -> (ind, i)
  | _ -> raise Not_found

let destCase t =
  match t.hd with
  | Case (ind, r) when List.is_empty t.args -> (ind, r)
  | _ -> raise Not_found

let destEvar t =
  match t.hd with
  | Evar i when List.is_empty t.args -> i
  | _ -> raise Not_found

(* Replaces t by \lambda^k. t, avoiding capture *)
let rec bump k t = if k = 0 then t else subst (fun i -> of_hd (Var (i + k))) t

(* Replaces every `Var i` in `t` by `fvar i`, avoiding capture. *)
and subst fvar t =
  let rec aux k t =
    mkApp (List.map (aux k) t.args)
      (match t.hd with
      | Var i when i < k -> of_hd t.hd
      | Const (_, _, _) -> of_hd t.hd
      | Type _ -> of_hd t.hd
      | Var i -> bump k (fvar (i - k))
      | Fun (forall, tele, body) ->
        let k, tele = List.fold_left_map (fun k (v, ty, t, impl) -> k+1, (v, aux k ty, Option.map (aux k) t, impl)) k tele in
        of_hd (Fun (forall, tele, aux k body))
      | Ind (v, a, c) ->
        of_hd (Ind (v, aux k a, List.map (aux (k+1)) c))
      | Construct (ind, id) -> of_hd (Construct (aux k ind, id))
      | Case (ind, r) -> of_hd (Case (aux k ind, r))
      | Evar i -> of_hd (Evar i)) in
  aux 0 t

(* [beta t t'] beta-reduces (\lambda. t') t *)
let beta t = subst (fun i -> if i = 0 then t else mkVar (i-1))

let is_ground t = try ignore (subst (fun _ -> raise Not_found) t); true with Not_found -> false

let rec of_kernel (t : Kernel.Term.t) =
  let open Kernel in
  let hd = match t.hd with
    | Term.Var i -> Var i
    | Term.Const (c, s, u) -> Const (c, s, u)
    | Term.Fun (f, tele, t) -> Fun (f, List.map (fun (v, ty, t, impl) -> (v, of_kernel ty, Option.map of_kernel t, impl)) tele, of_kernel t)
    | Term.Type s -> Type s
    | Term.Ind (v, a, c) -> Ind (v, of_kernel a, List.map of_kernel c)
    | Term.Construct (ind, i) -> Construct (of_kernel ind, i)
    | Term.Case (ind, r) -> Case (of_kernel ind, r) in
  { hd; args = List.map of_kernel t.args }

module Context_ = struct
  type t = context

  let empty = { univ = Kernel.Univ.Context.empty; var = IMap.empty; const = SMap.empty; evar = IMap.empty; hints = Pattern.Map.empty; flags = SMap.empty }
  let reset ctx = { ctx with univ = Kernel.Univ.Context.empty; var = IMap.empty; evar = IMap.empty }

  let depth ctx = match IMap.max_binding_opt ctx.var with | None -> 0 | Some (x, _) -> x + 1

  let push_var ?(avoid_capture=true) (v, ty, body, impl) ctx =
    let d = depth ctx in
    let v = if avoid_capture then Utils.fresh_name v (List.map (fun (_, (n, _, _, _)) -> n) (IMap.to_list ctx.var)) else v in
    { ctx with var = IMap.add d (v, ty, body, impl) ctx.var }, ()

  let with_var ?(avoid_capture=true) v f ctx =
    let ctx', () = push_var ~avoid_capture v ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var }, r)

  let fold_telescope ?(avoid_capture=true) f x tele k ctx =
    let ctx', r = List.fold_left (fun (ctx, x) (v, ty, t, impl) ->
      let v = if avoid_capture then Utils.fresh_name v (List.map (fun (_, (n, _, _, _)) -> n) (IMap.to_list ctx.var)) else v in
      let (ctx, r) = f x (v, ty, t, impl) ctx in
      fst (push_var ~avoid_capture:false (v, ty, t, impl) ctx), r) (ctx, x) tele in
    let ctx', r = k r ctx' in
    ({ ctx' with var = ctx.var }, r)

  module Monad = struct
    include CMonad

    module Head = struct
      let map ?(avoid_capture=false) f hd = match hd with
        | Var v -> ret (Var v)
        | Const (v, s, u) -> ret (Const (v, s, u))
        | Fun (x, tele, body) ->
          fold_telescope ~avoid_capture (fun rtele (v, ty, t, impl) ->
            let* ty = f ty in
            let+ t = Option.map f t in
            (v, ty, t, impl) :: rtele
          ) [] tele (fun rtele ->
            let+ body = f body in
            Fun (x, Utils.List.rev rtele, body))
        | Type u -> ret (Type u)
        | Ind (v, a, c) ->
          let* a' = f a in
          let+ c = with_var ~avoid_capture (v, a, None, false) (List.map f c) in
          Ind (v, a', c)
        | Construct (ind, i) -> let+ ind = f ind in Construct (ind, i)
        | Case (ind, i) -> let+ ind = f ind in Case (ind, i)
        | Evar i -> ret (Evar i)
    end
  end

  let univ ctx = ctx.univ

  let find_var i ctx =
    try IMap.find (depth ctx - i - 1) ctx.var with _ -> raise (TypeError (ctx, UnboundVar i))

  let find_const c ctx =
    try SMap.find c ctx.const with _ -> raise (TypeError (ctx, UnboundConst c))

  let find_evar i ctx =
    try IMap.find i ctx.evar with _ -> raise (TypeError (ctx, UnboundEvar i))

  let get_var_name i = let+* (v, _, _, _) = find_var i in v
  let get_var_type i = let+* (_, ty, _, _) = find_var i in bump (i + 1) ty
  let get_var_body i = let+* (_, _, t, _) = find_var i in Option.map (bump (i + 1)) t

  let var_depth = depth

  let get_const_univ c = let+* (u, _, _) = find_const c in u
  let get_const_type c = let+* (_, t, _) = find_const c in of_kernel t
  let get_const_body c = let+* (_, _, b) = find_const c in Option.map of_kernel b

  let get_evar_type i = let+* (t, _, _) = find_evar i in t
  let get_evar_body i = let+* (_, b, _) = find_evar i in b
  let get_evar_constraints i = let+* (_, _, c) = find_evar i in c


  let new_sort name ctx =
    let univ, s = Kernel.Univ.Context.new_sort name ctx.univ in
    { ctx with univ }, s

  let new_level name ctx =
    let univ, u = Kernel.Univ.Context.new_level name ctx.univ in
    { ctx with univ }, u


  (* TODO: propagate names *)
  let new_univ ctx =
    let univ, u = Kernel.Univ.Context.new_univ None None ctx.univ in
    { ctx with univ }, u

  let new_univs_with_constraints univs ctx =
    let univ, s = Kernel.Univ.Context.append univs ctx.univ in
    { ctx with univ }, s

  let add_sort_constraint s1 s2 ctx =
    let univ, () = Kernel.Univ.Context.add_sort_constraint s1 s2 ctx.univ in
    { ctx with univ }, ()

  let add_level_constraint u1 u2 ctx =
    let univ, () = Kernel.Univ.Context.add_level_constraint u1 u2 ctx.univ in
    { ctx with univ }, ()

  let add_univ_constraint u u' ctx =
    let univ, () = Kernel.Univ.Context.add_constraint u u' ctx.univ in
    { ctx with univ }, ()

  let push_telescope ?(avoid_capture=true) tele ctx =
    List.fold_left (fun ctx b -> fst (push_var ~avoid_capture b ctx)) ctx tele, ()

  let with_telescope ?(avoid_capture=true) tele f ctx =
    let ctx', () = push_telescope ~avoid_capture tele ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var }, r)

  let pop_var ctx =
    if IMap.is_empty ctx.var then raise (TypeError (ctx, UnboundVar 0)) else
    { ctx with var = IMap.remove (fst (IMap.max_binding ctx.var)) ctx.var }, ()

  let rec new_evar ?(ty=None) ?(with_ctx=true) =
    let* ty = match ty with
      | None -> let* u = new_univ in new_evar ~ty:(Some (mkType u)) ~with_ctx
      | Some ty -> Monad.ret ty in
    let** ty = fun ctx -> if with_ctx then mkForall (List.map snd (IMap.to_list ctx.var)) ty else ty in
    fun ctx ->
      let n = try fst (IMap.max_binding ctx.evar) + 1 with Not_found -> 0 in
      let d = depth ctx in
      { ctx with evar = IMap.add n (ty, None, []) ctx.evar}, { hd = Evar n; args = if with_ctx then (List.filter_map (fun (i, (_, _, t, _)) -> if t = None then Some (mkVar (d - i - 1)) else None) (IMap.to_list ctx.var)) else [] }

  let add_evar_constraint t1 t2 =
    let i = destEvar (of_hd t1.hd) in
    fun ctx -> { ctx with evar = IMap.update i (function | None -> raise (TypeError (ctx, (UnboundEvar i))) | Some (ty, t, cstrs) -> Some (ty, t, (ctx.var, t1, t2) :: cstrs)) ctx.evar }, ()

  let get_flag_opt flag ctx = SMap.find_opt flag ctx.flags
  let add_flag flag value ctx =
    { ctx with flags = SMap.add flag value ctx.flags }, ()
  let remove_flag flag ctx =
    { ctx with flags = SMap.remove flag ctx.flags }, ()

end

let fresh_const c =
  let** cuniv = Context_.get_const_univ c in
  let+ ((s, u), _) = Context_.new_univs_with_constraints cuniv in
  mkConst c s u

let rec fold ?(avoid_capture=true) ?(keep_evars=false) fold_hd fold_app t =
  let fold = fold ~avoid_capture ~keep_evars fold_hd fold_app in
  let default = 
    let* hd = Context_.Monad.Head.map ~avoid_capture fold t.hd in
    let* hd = fold_hd hd in
    let* args = Context_.Monad.List.map fold t.args in
    fold_app (hd :: args) in
  match t.hd with
  | Evar i when not keep_evars ->
    let targs = t.args in
    let** body = Context_.get_evar_body i in
    (match body with | None -> default | Some t ->
    let t = if not (List.is_empty t.args) then { t with args = t.args @ targs } else
      let n = min (match t.hd with | Fun (_, tele, _) -> List.length (List.take_while (fun (_, _, t, _) -> Option.is_none t) tele) | _ -> 0) (List.length targs) in
      let hd = match t.hd with | Fun (f, tele, body) -> mkForallOrFun f (List.drop n tele) body | _ -> t in
      let args, rest = List.split_at n targs in
      let args = IMap.of_list (List.mapi (fun i arg -> (i, arg)) (List.rev args)) in
      let n = Option.map_or 0 (fun n -> fst n + 1) (IMap.max_binding_opt args) in
      let t = subst (fun v -> try IMap.find v args with _ -> mkVar (v - n)) hd in
      { t with args = t.args @ rest } in
    fold t)
  | _ -> default

let print ?(keep_evars=false) ?(debug=false) t =
  let (+) = String.cat in
  let ret = Context_.Monad.ret in
  let rec fold_hd = function
    | Var v -> if debug then ret ("_" + string_of_int v, true) else fun ctx -> let c = try Context_.get_var_name v ctx with _ -> "_" + string_of_int v in ctx, (c, true)
    | Const (c, s, u) -> ret (c + "@{" + String.concat ", " (List.map Kernel.Univ.Sort.print s) + ";" + String.concat ", " (List.map Kernel.Univ.Level.print u) + "}", true)
    | Fun (forall, (v, ty, Some t, _) :: tele, body) -> let+ (body, _) = if List.is_empty tele then ret body else fold_hd (Fun (forall, tele, body)) in ("let " + v + " : " + (fst ty) + " := " + (fst t) + " in " + body, false)
    | Fun (forall, tele, body) -> ret ((if forall then "forall " else "fun ") + String.concat " " (List.map (fun (v, ty, _, impl) ->
        (if impl then "{" else "(") + v + " : " + fst ty + (if impl then "}" else ")")
      ) tele) + (if forall then ", " else " => ") + fst body, false)
    | Type u -> ret (Kernel.Univ.print u, true)
    | Ind (v, a, c) -> ret ("ind " + v + " : " + fst a + " :=" + " | " + String.concat " | " (List.map fst c), false)
    | Construct (ind, id) -> ret ("ind.mk(" + fst ind + ")." + string_of_int id, true)
    | Case (ind, recursive) -> ret ((if recursive then "ind.fix(" else "ind.case(") + fst ind + ")", true)
    | Evar i -> ret ("?" + string_of_int i, true) in
  let+* (t, _) = Context_.Monad.to_imut (fold ~avoid_capture:false ~keep_evars fold_hd
    (function
      | [hd] -> ret hd
      | args -> ret (String.concat " " (List.map (fun (t, atomic) -> if atomic then t else "(" + t + ")") args), false)) t) in
  t

let print_type_error e ctx =
  let (+) = String.cat in
  match e with
  | UnboundVar i -> "Unbound variable " + string_of_int i + "\n"
  | UnboundConst v -> "Unbound constant " + v + "\n"
  | UnboundEvar v -> "Unbound evar " + string_of_int v + "\n"
  | NotAType t -> print t ctx + " is not a type\n"
  | IllegalApplication t -> "Illegal application in " + print t ctx + "\n"
  | TypeMismatch (ty, t) ->
    "Term " + print t ctx + " does not have type " + print ty ctx + "\n"
  | IllFormed t -> print t ctx + " is ill-formed\n"
  | NoBody t -> print t ctx + "has no body\n"
  | NotGround t -> print t ctx + "is not ground\n"
  | IllegalConstructorReturnType t -> "Constructor should return an element of the inductive type, but has type " + print t ctx + "\n"
  | NonPositive t -> "Constructor of type " + print t ctx + " is not positive\n"
  | PropElimination t -> "Cannot eliminate " + print t ctx + "outside of Prop\n"
  | HO (l, r) -> "Higher order unification : " + print l ctx + " =~= " + print r ctx + "\n"
  | OccurCheck (l, r) -> "OccurCheck : " + print l ctx + " =~= " + print r ctx + "\n"
  | CannotUnify (l, r) -> "Cannot unify : " + print l ctx + " =~= " + print r ctx + "\n"

let free_vars =
  let (+) = ISet.union in
  let rec aux k t =
    let hd = match t.hd with
      | Var v when k <= v -> ISet.singleton (v - k)
      | Fun (_, tele, body) ->
        let k, f = List.fold_left (fun (k, f) (_, ty, t, _) -> Int.(k + 1), f + aux k ty + Option.map_or ISet.empty (aux k) t) (k, ISet.empty) tele in
        f + aux k body
      | Ind (_, a, c) -> List.fold_left (+) (aux k a) (List.map (aux Int.(k + 1)) c)
      | Construct (ind, _) | Case (ind, _) -> aux k ind
      | _ -> ISet.empty in
    List.fold_left (+) hd (List.map (aux k) t.args) in
  aux 0

let free_univs t =
  let (+) = fun (fs1, fu1) (fs2, fu2) -> (ISet.union fs1 fs2, ISet.union fu1 fu2) in
  let ret = Context_.Monad.ret in
  Context_.Monad.to_imut (fold (fun hd -> ret (match hd with
    | Var _ | Evar _ -> (ISet.empty, ISet.empty)
    | Type (s, u) -> (Kernel.Univ.Sort.free_vars s, Kernel.Univ.Level.free_vars u)
    | Const (_, s, u) -> List.fold_left ISet.union ISet.empty (List.map Kernel.Univ.Sort.free_vars s), List.fold_left ISet.union ISet.empty (List.map Kernel.Univ.Level.free_vars u)
    | Fun (_, tele, body) -> List.fold_left (+) body (List.map (fun (_, ty, t, _) -> match t with | None -> ty | Some t -> ty + t) tele)
    | Ind (_, a, c) -> List.fold_left (+) a c
    | Construct (ind, _) | Case (ind, _) -> ind))
    (fun args -> ret (List.fold_left (+) (ISet.empty, ISet.empty) args)) t)

let rec eq t t' =
  let ret = Context_.Monad.iret in
  let (&&) a b = let** a = a in if a then b else ret false in
  let (||) a b = let** a = a in if a then ret true else b in 

  ret (List.length t.args = List.length t'.args) &&
  (match t.hd, t'.hd with
  | Var v, Var w -> ret (v = w)
  | Const (c, s, u), Const (c', s', u') ->  ret (c = c') && ret (s = s') && ret (u = u')
  | Fun (f, t, b), Fun (f', t', b') -> ret (f = f') &&
    (ret (List.length t = List.length t')) &&
    Context_.Monad.to_imut (Context_.Monad.List.for_all2 (fun (_, ty, t, _) (_, ty', t', _) -> Context_.Monad.to_mut (eq ty ty' &&
    match t, t' with
    | None, None -> ret true
    | Some t, Some t' -> eq t t'
    | _, _ -> ret false)) t t') &&
    eq b b'
  | Type u, Type u' -> ret (u = u')
  | Ind (v, a, c), Ind (_, a', c') -> (ret (List.length c = List.length c')) && eq a a' && Context_.Monad.to_imut (Context_.with_var (v, a, None, false) (Context_.Monad.List.for_all2 (fun t t' -> Context_.Monad.to_mut (eq t t')) c c'))
  | Construct (ind, i), Construct (ind', i') -> ret (i = i') && eq ind ind'
  | Case (ind, r), Case (ind', r') -> ret (r = r') && eq ind ind'
  | Evar i, Evar j -> ret (i = j) ||
    let** t = Context_.get_evar_body i in
    let** t' = Context_.get_evar_body j in
    (match t, t' with
    | Some t, Some t' -> eq t t'
    | _, _ -> ret false)
  | _, _ -> ret false) &&
  Context_.Monad.to_imut (Context_.Monad.List.for_all2 (fun t t' -> Context_.Monad.to_mut (eq t t')) t.args t'.args)

let prefix t' t =
  let (&&) a b = let** a = a in if a then b else Context_.Monad.iret false in
  Context_.Monad.iret (List.length t.args < List.length t'.args) &&
  eq { t with args = List.take (List.length t'.args) t.args } t'

(* Checks whether `t'` occurs in `t`. *)
let occurs t' t =
  let ret = Context_.Monad.iret in
  let (||) a b = let** a = a in if a then ret true else b in 
  let rec aux t' t =
    prefix t' t ||
    (match t.hd with
    | Var _ | Type _ | Const _ -> ret false
    | Fun (_, tele, body) ->
      let* t' = Context_.Monad.List.fold_left (fun (_, ty, t, _) t' ->
        match t' with | None -> Context_.Monad.ret None
        | Some t' ->
        let+ b = Context_.Monad.List.exists (fun t -> Context_.Monad.to_mut (aux t' t)) (ty :: Option.to_list t) in
        if b then None else Some (bump 1 t')) tele (Some t') in
      (match t' with | None -> ret true | Some t' -> aux t' body)
    | Ind (_, arity, constructors) ->
      aux t arity || Context_.Monad.to_imut (Context_.Monad.List.exists (fun t -> Context_.Monad.to_mut (aux (bump 1 t') t)) constructors)
    | Construct (ind, _) | Case (ind, _) -> aux t ind
    | Evar i ->
      let** body = Context_.get_evar_body i in
      match body with | None -> ret false
      | Some t -> aux t' t) ||
    Context_.Monad.to_imut (Context_.Monad.List.exists (fun t -> Context_.Monad.to_mut (aux t' t)) t.args) in
  aux t' t

let subst_univ ss su t =
  Context_.Monad.to_imut (fold (fun t -> Context_.Monad.ret @@ of_hd (match t with
    | Const (c, s, u) -> Const (c, List.map (Kernel.Univ.Sort.subst ss) s, List.map (Kernel.Univ.Level.subst su) u)
    | Type (s, u) -> Type (Kernel.Univ.Sort.subst ss s, Kernel.Univ.Level.subst su u)
    | t -> t))
    (function | [] -> failwith "unreachable" | t :: args -> Context_.Monad.ret { hd = t.hd; args }) t)

let to_pattern t =
  let ret = Context_.Monad.ret in
  Context_.Monad.to_imut (fold ~avoid_capture:false ~keep_evars:false (fun hd -> ret @@ Pattern.of_hd
    (match hd with
    | Var i -> Pattern.Var i
    | Const (v, _, _) -> Pattern.Const v
    | Fun (f, tele, body) -> Pattern.Fun (f, List.map (fun (_, ty, t, _) -> (ty, t)) tele, body)
    | Type _ -> Pattern.Type
    | Ind (_, a, c) -> Pattern.Ind (a, c)
    | Construct (ind, i) -> Pattern.Construct (ind, i)
    | Case (ind, r) -> Pattern.Case (ind, r)
    | Evar _ -> Pattern.Any))
  (fun args -> ret { Pattern.hd = (List.hd args).hd; Pattern.args = List.tl args })
  t)

let get_hints t ctx =
  let t = to_pattern t ctx in
  let hints = Pattern.Map.find_all ctx.hints t in
  List.map of_kernel hints

type cumulativity = Conv | Cumul | Cocumul
let swap_cumulativity = function
  | Conv -> Conv
  | Cumul -> Cocumul
  | Cocumul -> Cumul

(* TODO: find better names. *)
type until = | Max | Exact of int | AtMost of int
let until_take n = function
  | Max -> Max
  | Exact m -> Exact (m - n)
  | AtMost m -> AtMost (m - n)
let until_opt = function | Max -> None | Exact n | AtMost n -> Some n

let synthesize : (t -> unit Context_.Monad.t) ref = ref (fun _ -> assert false)

type whd_flags = {
  beta    : bool;
  delta   : bool;
  eta     : bool;
  iota    : bool;
  zeta    : bool;
  iota_all: bool;
  steps    : int option;
}
  
let whd_flags_none = {
  beta     = false;
  delta    = false;
  eta      = false;
  iota     = false;
  zeta     = false;
  iota_all = false;
  steps     = None;
}

let whd_flags_all = {
  beta     = true;
  delta    = true;
  eta      = true;
  iota     = true;
  zeta     = true;
  iota_all = true;
  steps     = None;
}

let whd_flags_step flags =
  { flags with steps = Option.map (fun i -> i - 1) flags.steps }

(* [eta t] tells how many eta-reductions can be done on `t` *)
let eta ?(steps=None) t =
  (* TOTHINK: What should be checked by the caller? *)
  let () = assert (steps <> Some 0 && List.length t.args = 0) in
  match t.hd with
  | Fun (false, tele, body) when List.for_all (fun (_, _, t, _) -> Option.is_none t) tele -> 
    let n = List.length tele in
    let steps = Option.map_or n (min n) steps in
    let rec rm_tail i args =
      if i = steps then i, args else
      match args with
      | { hd = Var j; args = [] } :: args when j = i -> rm_tail (i + 1) args
      | args -> i, args in
    let ntail, rargs = rm_tail 0 (List.rev body.args) in
    if ntail = 0 then None else
    let args = List.rev rargs in
    (match ISet.min_elt_opt (free_vars { hd = body.hd; args }) with
      | Some 0 -> None
      | Some j when j < ntail -> 
        Some (of_hd (Fun (false, List.take (n - j) tele, { body with args = args @ (List.init (ntail - j) (fun i -> mkVar (ntail - i - 1))) })), j)
      | _ -> Some (of_hd (Fun (false, List.take (n - ntail) tele, { body with args })), ntail))
  | _ -> None

(* [iota t ctx] iota-reduces `t`, i.e. turns `App (Case (App (ind :: indargs), r) :: ret :: branches @ [App (Construct (ind, i) :: sargs)]` into:
  - `App (List.nth branches i :: indargs @ sargs` if `r` is `false` (non-recursive match)
  - `App (List.nth branches i :: indargs @ sargs @ rargs` with `args` being recursive calls on the elements of `sargs` that are from the inductive type being matched against if `r` is `true` (recursive match) *)

let rec iota ?(flags=whd_flags_all) t : t option Context_.Monad.it =
  let { hd = h; args } = t in
  match destCase (of_hd h) with
  | exception Not_found -> Context_.Monad.iret None
  | ind, recursive ->
  let** { hd = ind; args = aargs } = whd ind in
  let** (v, a, c) = fun ctx -> try destInd (of_hd ind) with Not_found -> raise (TypeError (ctx, IllFormed (of_hd h))) in
  let nc = List.length c in
  (* Getting the subject. *)
  match List.split_at (1 + nc) args with
  | exception Not_found | _, [] -> Context_.Monad.iret None
  | objs, subject :: eargs ->
  let** { hd = ci; args = sargs } = whd ~flags:(if flags.iota_all then whd_flags_all else flags) subject in
  match destConstruct (of_hd ci) with
  | exception Not_found -> Context_.Monad.iret None
  | _, i ->
  let** rargs =
    if not recursive then Context_.Monad.iret [] else
    Context_.Monad.to_imut (Context_.with_var ~avoid_capture:false (v, a, None, false) (
    let* ctele, _ = destArity (List.nth c i) in
    let* _, rargs = Context_.fold_telescope ~avoid_capture:false (fun (iarg, rargs) (_, arg, _, _) ->
      let** { hd; args } = whd arg in
      Context_.Monad.ret (iarg+1,
      match hd with
      | Var i when i = iarg ->
        let args = List.map
          (subst (fun i ->
            if i < iarg then List.nth sargs (iarg-1-i) else
            of_hd (if i = iarg then ind else Var i)))
          args in
        { hd = Case ({ hd = ind; args }, recursive); args = objs @ [List.nth sargs iarg] } :: rargs
      | _ -> rargs)) (0, []) ctele Context_.Monad.ret in
    Context_.Monad.ret (List.rev rargs))) in
  let targs = aargs @ sargs @ rargs @ eargs in
  Context_.Monad.iret (Some (mkApp targs (List.nth objs (1+i))))

and whd_opt ?(flags=whd_flags_all) t : t option Context_.Monad.it =
  (*let** () = let+* t = print t in print_endline ("whd " ^ t) in*)
  let ret = Context_.Monad.iret in
  if flags.steps = Some 0 then ret None else
  match t.hd with
  | Var i when flags.delta ->
(*     let () = print_endline "var" in *)
    let** body = Context_.get_var_body i in
    (match body with
    | None -> ret None
    | Some body ->
    let t = mkApp t.args body in
    let+* t = whd ~flags:(whd_flags_step flags) t in
    Some t)
  | Const (c, s, u) when flags.delta ->
(*     let () = print_endline "const" in *)
    let** body = Context_.get_const_body c in
    (match body with
    | None -> ret None
    | Some body ->
    let ss = List.fold_left (fun ss (i, s) -> IMap.add i s ss) IMap.empty (List.mapi (fun i s -> (i, s)) s) in
    let su = List.fold_left (fun su (i, u) -> IMap.add i u su) IMap.empty ((0, Kernel.Univ.Level.base) :: List.mapi (fun i u -> (i + 1, u)) u) in
    let** body = subst_univ ss su body in
    let t = mkApp t.args body in
    let+* t = whd ~flags:(whd_flags_step flags) t in
    Some t)
  (* Free normalization, preparing for eta reductions *)
  | Fun (false, tele, { hd = Fun (false, tele', body); args = [] }) ->
    let rec get_teles rteles = function
      | { hd = Fun (false, tele, body); args = [] } -> get_teles (tele :: rteles) body
      | t -> rteles, t in
    let rteles, body = get_teles [] body in
    whd_opt ~flags { hd = Fun (false, List.concat (tele :: tele' :: List.rev rteles), body); args = t.args }
  | Fun (f, (_, _, Some b, _) :: tele, body) when flags.zeta ->
(*     let () = print_endline "zeta" in *)
    let t = mkApp t.args (beta b (mkForallOrFun f tele body)) in
    let+* t = whd ~flags:(whd_flags_step flags) t in
    Some t
  | Fun (false, (_, _, None, _) :: tele, body) when flags.beta && not (List.is_empty t.args) ->
(*     let () = print_endline "beta" in *)
    (match t.args with | [] -> failwith "unreachable" | a :: args ->
    let t = mkApp args (beta a (mkFun tele body)) in
    let+* t = whd ~flags:(whd_flags_step flags) t in
    Some t)
  | Fun (false, tele, body) when flags.eta && List.is_empty t.args ->
(*     let () = print_endline "eta" in *)
    let t = mkFun tele body in
    (match eta t with | None -> ret None | Some (t, n) ->
    let+* t = whd ~flags:{ flags with steps = Option.map (fun k -> k - n) flags.steps } t in
    Some t)
  | Case (_, _) when flags.iota ->
(*     let () = print_endline "iota" in *)
    let** t' = iota ~flags t in
    (match t' with | None -> ret None | Some t ->
    let+* t = whd ~flags:(whd_flags_step flags) t in
    Some t)
  | Evar i ->
(*     let () = print_endline ("evar " ^ string_of_int i) in *)
    let** b = Context_.get_evar_body i in
    (match b with | None -> ret None | Some b ->
    let steps = Some (match b.hd with | Fun (false, tele, _) when List.is_empty b.args -> List.length tele | _ -> 0) in
    let t = mkApp t.args b in
    let** t= whd ~flags:{ whd_flags_none with beta = true; steps } t in
    let+* t = whd ~flags t in
    Some t)
  | _ -> ret None

and whd ?(flags=whd_flags_all) t =
  let+* t' = whd_opt ~flags t in
  Option.value ~default:t t'

(* Splits `forall x1 ... xk, ty` into `[x1; ...; xn], forall x(n+1) ... xk, ty`. If `n` is None, takes the longest list possible. *)
(* TODO: This is in quadratic time, I may be able to optimize by taking care of the zeta-redexes by hand. *)
and destArity ?(whd_rty=false) ?(keep_let=false) ?(until=Max) ?(count_implicits=true) ?(trailing_implicits=false) (t : t) : (t telescope * t) Context_.Monad.t =
  let** debug = Context_.get_flag_opt "debug-synthesis" in
  let** () = if Option.is_some debug then let+* t = print t in print_endline ("destArity " ^ (match until with | Max -> "= oo" | Exact n -> "= " ^ string_of_int n | AtMost n -> "<= " ^ string_of_int n) ^ " " ^ t) else Context_.Monad.iret () in
  let ret = Context_.Monad.ret in
  let flags = { whd_flags_all with zeta = not keep_let } in
  let rec aux until rtele t =
    if not trailing_implicits && until_opt until = Some 0 then let** t = if whd_rty then whd t else Context_.Monad.iret t in ret (rtele, t) else
    let** t' = whd ~flags t in
    match t'.hd with
    | Fun (true, (_, _, _, false) :: _, _) when until_opt until = Some 0 -> ret (rtele, if whd_rty then t' else t)
    | Fun (true, ((_, _, _, impl) as b) :: tele, body) ->
      Context_.with_var ~avoid_capture:false b (aux (if impl && not count_implicits then until else until_take 1 until) (b :: rtele) (mkForall tele body))
    | _ when match until with | Exact n when 0 < n -> false | _ -> true -> ret (rtele, if whd_rty then t' else t)
    | Evar _ ->
      let rec loop rtele until =
        let* u = Context_.new_univ in
        let* ty = Context_.new_evar ~ty:(Some (mkType u)) ~with_ctx:true in
        if until_opt until = Some 0 then Context_.Monad.ret (rtele, ty) else
        let b = ("x", ty, None, false) in
        Context_.with_var ~avoid_capture:false b (loop (b :: rtele) (until_take 1 until)) in
      let* rtele, ty = loop [] until in
      let tele = List.rev rtele in
      let+ () = instantiate_evar t' (mkForall tele ty) in
      tele, ty
    | _ -> fun ctx -> raise (TypeError (ctx, IllegalApplication t)) in
  let+ rtele, t  = aux until [] t in
  List.rev rtele, t

and fold_left_args_with_type args ty f acc =
(*   let** () = let* args = Context_.Monad.List.map (fun t -> Context_.Monad.to_mut (print t)) args in let+* ty = print ty in print_endline ("fold_left_args " ^ String.concat " " args ^ " with type " ^ ty) in *)
  if List.is_empty args then Context_.Monad.ret (acc, ty) else
  let args' = Dynarray.create () in
  let subst t =
    let n = Dynarray.length args' in
    if n = 0 then t else subst (fun i -> if i < n then Dynarray.get args' (n - i - 1) else mkVar (i - n)) t in
  let* tele, ty = destArity ~whd_rty:false ~until:(AtMost (List.length args)) ty in
  if List.is_empty tele then fun ctx -> raise (TypeError (ctx, IllegalApplication ty)) else
  let args, rargs = List.split_at (List.length tele) args in
  let* acc = Context_.Monad.List.fold_left (fun (arg, (_, ty, _, _)) acc ->
    let ty = subst ty in
    let+ arg, acc = f arg ty acc in
    let () = Dynarray.add_last args' arg in
    acc
  ) (List.combine args tele) acc in
  let ty = subst ty in
  fold_left_args_with_type rargs ty f acc

(* [instantiate_evar ev t] asserts that [ev] is of the form [(Evar i) args] and defines the body of evar [i] with [t], capturing the subterms of [t] that appear in [args]
    Heuristc: When there are several ways to capture subterms, we capture the largests first and then from the last argument to the first argument and then from the last element of the context to the first. *)
and instantiate_evar { hd = ev; args } t =
  (*let () = print_endline ("instantiate_evar") in*)
  let ret = Context_.Monad.ret in
  let iret = Context_.Monad.iret in

  let i = destEvar (of_hd ev) in
  let** (ity, ibody, icstrs) = Context_.find_evar i in
  if ibody <> None then failwith "Anomaly: instantiating already instantiated evar." else

  (* Checking that the instantiation is well-typed. *)
  let* ty = typecheck { hd = ev; args } in
  let* tty = typecheck t in
  let* b = unify ty tty in
  if not b then fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) else

  let* map =
    Context_.Monad.List.fold_left (fun (i, arg) map ->
      let+ j = try ret (destVar arg) with _ -> fun ctx -> raise (TypeError (ctx, HO ({ hd = ev; args }, t))) in
      IMap.update j (function | None -> Some (Some i) | Some _ -> Some None) map
    ) (List.mapi (fun i arg -> (i, arg)) (List.rev args)) IMap.empty in

  let t' = t in
  let** d = Context_.depth in
  let pbevars = ref (ISet.singleton i) in
  let evarsty = ref IMap.empty in
  (* Getting rid of the variables that are not in `args`. *)
  let* t = rm_problematic_term ~instantiate_evars:true (fun t ->
    let** d' = Context_.depth in
    match t.hd with
    | Var v when d' <= v -> fun ctx -> raise (TypeError (ctx, UnboundVar (v - d')))
    | Var v when d' - d <= v -> iret (Option.is_none (IMap.find_opt (v - (d' - d)) map))
    (* Avoiding instantiation loops. *)
    | Evar j when ISet.mem j !pbevars -> iret true
    (* Avoiding loops in evar's types. *)
    | Evar j when IMap.mem j !evarsty -> iret false
    | Evar j ->
      let** ty = Context_.get_evar_type j in
      let* ty = rm_problematic_term ~instantiate_evars:false (fun t ->
        match t.hd with
        | Evar j when j = i -> iret true
        | _ -> iret false) ty in
      (match ty with
      | None -> let () = pbevars := ISet.add j !pbevars in iret true
      | Some ty -> let () = evarsty := IMap.add j ty !evarsty in iret false)
    | _ -> iret false
  ) t in
  match t with
  | None -> fun ctx -> raise (TypeError (ctx, OccurCheck ({ hd = ev; args }, t')))
  | Some t ->
  (* Getting rid of the variables that cause the instantiation to be higher-order. *)
  let* t = rm_problematic_term (fun t ->
    let** d' = Context_.depth in
    match t.hd with
    | Var v when d' <= v -> failwith "unreachable"
    | Var v when d' - d <= v -> iret (Option.is_none (IMap.find (v - (d' - d)) map))
    | _ -> iret false
  ) t in
  match t with
  | None -> fun ctx -> raise (TypeError (ctx, HO ({ hd = ev; args }, t')))
  | Some t ->
  let* () = fun ctx -> { ctx with evar = IMap.merge (fun _ ev ty' -> match ty' with | None -> ev | Some ty -> let (_, t, cstr) = Option.get ev in Some (ty, t, cstr)) ctx.evar !evarsty }, () in
  let t = subst (fun i -> mkVar (Option.get (IMap.find i map))) t in
  let** ty = Context_.get_evar_type i in
  let* (tele, _) = destArity ~whd_rty:false ~until:(Exact (List.length args)) ty in fun ctx ->
  let ctx = { ctx with evar = IMap.update i (fun _ -> Some (ity, Some (mkFun tele t), [])) ctx.evar } in
  List.fold_left (fun (ctx, ()) (var, l, r) -> let cvar = ctx.var in let ctx, b = unify l r { ctx with var } in if b then { ctx with var = cvar }, () else raise (TypeError (ctx, CannotUnify (l, r)))) (ctx, ()) icstrs

(* Attempt at writing a HO instantiation, I stopped at the fact that I can not compute the expected type of some subterms, so I can not decide which replacement to make.
  let* ty = typecheck (of_hd ev) in
  let n = List.length args in
  let* (tele, _) = destArity ~until:(Exact n) ty in
  let args = List.rev (List.combine args (List.map (fun (_, ty, _) -> ty) tele)) in

  (* From now on, we have two contexts, the one where `t` is well-typed and the one where the result of the compilation of `t` is well-typed.
    By convention, I will put a prime on the objects related to the latter context. *)
  let ctx' = { ctx with var = tele } in

  (* Substitute `t` of expected type `ty` under `k` binders. *)
  let subst k ty' t ctx ctx' =
    let rec aux i ctx ctx' = function
    | [] -> ctx', None
    | (argty', arg) :: l ->
      let arg = bump k arg in
      if not (prefix arg t ctx) then aux (i + 1) l ctx ctx' else
      let ctx', b = match ty' with | None -> ctx', true | Some ty' -> unify ty' (bump k argty') ctx' in
      if not b then aux (i + 1) l ctx ctx' in
      let args = List.drop (List.length arg) t.args in
      ctx', (Some (mkVar (n - i - 1 + k), args)) in
    aux 0 args in

  let rec fold k ty' t ctx ctx' =
    let ctx', t' = subst k ty' t ctx ctx' in
    match t' with
    | Some (t', args) ->
      let ctx', ty' = typecheck t' ctx' in
      let ctx', ((ctx, args'), _) = fold_left_args_with_type args ty' (fun arg ty' (ctx, args') ctx' ->
        let ctx, arg' = fold k (Some ty') arg ctx ctx' in
        { ctx with var = ctx'.var }, (arg', (ctx, arg' :: args'))
      ) (ctx, args') in
      ctx, mkApp args' t'
    | None ->
      let ctx, t' = (match t.hd with
      | Var _ -> raise Not_found (* We should capture all variables *)
      | (Const _ as t') | (Type _ as t') -> ctx, t'
      | Fun (f, tele, body) ->
        let rec fold_tele k tele' ctx ctx' = function
          | [] -> ctx, ctx', k, tele'
          | (v, ty, t) :: tele ->
            (* We can not get the expected type for `ty`, so let us just ignore the type constraint. *)
            let ctx, ty' = fold k None ty ctx { ctx with var = ctx'.var } in
            let ctx, t' = match t with | None -> ctx, t | Some t -> fold k (Some ty') t ctx { ctx with var = ctx'.var } in
            let ctx' = { ctx with var = ctx'.var } in
            fold_tele (k + 1) ((v, ty', t') :: tele') (fst (Context_.push_var ~avoid_capture:false (v, ty, t) ctx)) (fst (Context_.push_var ~avoid_capture:false (v, ty', t') ctx'))
        let var, var' = ctx.var, ctx'.var in
        let ctx, ctx', k, tele' = fold_tele k tele' ctx ctx' in
        (* We can not get the expected type for `body, so let us just ignore the type constraint. *)
      | Fun ([], body) -> fold body
      | Fun ((s, arg) :: tele, body) -> 
        let* arg = fold arg in
        let+ t = under_binder (fold (Fun (tele, body))) in
        mkFun [s, arg] t
      | App l -> (fun ctx ->
        let ctx, l = List.fold_left_map (fun ctx t -> fold t ctx) ctx l in
        ctx, App l)
      | Pi ([], body) -> fold body
      | Pi ((s, arg) :: tele, body) -> 
        let* arg = fold arg in
        let+ t = under_binder (fold (Pi (tele, body))) in
        mkPi [s, arg] t
      | Let (s, ty, body, t) ->
        let* ty = fold ty in
        let* body = fold body in
        let+ t = under_binder (fold t) in
        Let (s, ty, body, t)
      | Ind (v, ind, c) ->
        let* ind = fold ind in (fun ctx ->
        let ctx, c = List.fold_left_map (fun ctx t -> fold t ctx) ctx c in
        ctx, Ind (v, ind, c))
      | Construct (ind, i) -> let+ ind = fold ind in Construct (ind, i)
      | Case (ind, r) -> let+ ind = fold ind in Case (ind, r)
      | Evar (j, jctx) ->
        (* FIXME: Do I get the right side-effect on js? *)
        let** js = Context_.get_evar_context j in
        let js = Array.copy js in
        let+ jctx = fun ctx -> Array.fold_left_map (fun ctx (i, t) ->
          if not js.(i) then ctx, t else
          try fold t ctx
          with Not_found -> let () = js.(i) <- false in ctx, t) ctx (Array.combine (Array.init (Array.length jctx) (fun i -> i)) jctx) in
        Evar (j, jctx)) in
  let* t = fold t in
  let* t =
    let n = List.length args in
    if n = 0 then Context_.Monad.iret t else
    let+ tele, _ = destArity ity in
    let tele, _ = List.split_at n tele in
    mkFun tele t in
  fun ctx -> { ctx with evar = IMap.add i (is, ity, Some t) ctx.evar }, ()
  *)

and unify ?(cumulative=Conv) t1 t2 =
  let timestamp = timestamp () in let _ = timestamp in
  let ret = Context_.Monad.ret in

  (* Boolean combinators that restore the initial context when they return false. *)
  let (&&) state f = fun ctx ->
    let ctx', b = state ctx in
    if not b then ctx, false else
    let ctx', b = f ctx' in
    (if b then ctx' else ctx), b in
  let (||) state f = fun ctx ->
    let ctx', b = state ctx in
    if b then ctx', b else
    let ctx', b = f ctx in
    (if b then ctx' else ctx), b in

  (* unifies t1 and t2 without reducing either. *)
  let rigid ?(cumulative=Conv) t1 t2 =
    (match t1.hd, t2.hd with
    | Var i, Var j | Evar i, Evar j -> ret (i = j)
    | Const (c, s, u), Const (c', s', u') ->
      ret (c = c') &&
      (if cumulative = Cocumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun s s' -> let+ () = Context_.add_sort_constraint s s' in true) s s' ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun s s' -> let+ () = Context_.add_sort_constraint s s' in true) s' s ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cocumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun u u' -> let+ () = Context_.add_level_constraint u u' in true) u u' ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun u u' -> let+ () = Context_.add_level_constraint u u' in true) u' u ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false))
    | Type u, Type u' -> 
      (if cumulative = Cocumul then ret true else (fun ctx -> try (let+ () = Context_.add_univ_constraint u u' in true) ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try (let+ () = Context_.add_univ_constraint u' u in true) ctx with Kernel.Univ.UnivError (univ, _) -> { ctx with univ }, false))
    | Fun (f, (v, ty, t, impl) :: tele, body), Fun (f', (_, ty', t', _) :: tele', body') ->
      ret (f = f') &&
      unify ty ty' &&
      (match t, t' with
      | None, None -> ret true
      | Some t, Some t' -> unify t t'
      | _, _ -> ret false) &&
      Context_.with_var ~avoid_capture:false (v, ty, t, impl) (unify (mkForallOrFun f tele body) (mkForallOrFun f' tele' body'))
    | Ind (v, a, c), Ind (_, a', c') ->
      unify a a' && (ret (List.length c = List.length c')) && Context_.with_var (v, a, None, false) (Context_.Monad.List.for_all2 unify c c')
    | Construct (ind, i), Construct (ind', i') ->
      ret (i = i') && unify ind ind'
    | Case (ind, r), Case (ind', r') ->
      ret (r = r') && unify ind ind'
    | _, _ -> ret false) &&
    (ret (List.length t1.args = List.length t2.args)) &&
    Context_.Monad.List.for_all2 unify t1.args t2.args in

  let whd t =
    let** t' = whd_opt ~flags:{ whd_flags_none with delta = true; steps = Some 1 } t in
    let t, progress = match t' with | None -> t, false | Some t -> t, true in
    let+* t' = whd_opt ~flags:{ whd_flags_all with delta = false } t in
    let t, progress = match t' with | None -> t, progress | Some t -> t, true in
    if progress then Some t else None in

  let rec aux ~cumulative o1 o2 t1 t2 =
     let** debug = Context_.get_flag_opt "debug-unification" in
     let debug = Option.is_some debug in
     let** () =
       if not debug then Context_.Monad.iret () else
       let** t1 = print t1 in
       let+* t2 = print t2 in
       print_endline (timestamp ^ ": " ^ t1 ^ (match cumulative with | Conv -> " =~= " | Cumul -> " <~= " | Cocumul -> " >~= ") ^ t2) in
    let** b = eq t1 t2 in
    if b then ret true else
    rigid ~cumulative t1 t2 ||
    let** t2' = whd t2 in
    match t2' with | Some t2 -> aux ~cumulative o1 o2 t1 t2 | None ->
    let** t1' = whd t1 in
    (match t1' with | Some t1 -> aux ~cumulative o1 o2 t1 t2 | None -> 
    match t1.hd, t2.hd with
    | Evar i, Evar j when i = j ->
      (* The arguments do not unify, postponing is more precise than removing the corresponding arguments from the telescope. *)
      let* () = Context_.add_evar_constraint t1 o2 in
      let+ () = Context_.add_evar_constraint t2 o1 in
      true
    | Evar _, Evar _ -> fun ctx ->
      (try let ctx, () = instantiate_evar t1 o2 ctx in ctx, true
      with | TypeError (_, (HO (_, _))) | TypeError (_, (OccurCheck (_, _))) ->
        (try let ctx, () = instantiate_evar t2 o1 ctx in ctx, true
        with | TypeError (_, (HO (_, _))) | TypeError (_, (OccurCheck  (_, _))) ->
          let ctx, () = Context_.add_evar_constraint t1 o2 ctx in
          let ctx, () = Context_.add_evar_constraint t2 o1 ctx in
          ctx, true
        | TypeError (_, _) -> ctx, false)
      | TypeError (_, _) -> ctx, false)
    | Evar _, _ -> fun ctx -> 
      (try let ctx, () = instantiate_evar t1 o2 ctx in ctx, true
      with | TypeError (_, (HO (_, _))) | TypeError (_, (OccurCheck (_, _))) ->
        let ctx, () = Context_.add_evar_constraint t1 o2 ctx in
        ctx, true
      | TypeError (_, _) -> ctx, false)
    | _, Evar _ -> fun ctx ->
      (try let ctx, () = instantiate_evar t2 o1 ctx in ctx, true
      with | TypeError (_, (HO (_, _))) | TypeError (_, (OccurCheck (_, _))) ->
        let ctx, () = Context_.add_evar_constraint t2 o1 ctx in
        ctx, true
      | TypeError (_, _) -> ctx, false)
    | _, _ -> ret false
  ) in
  aux ~cumulative t1 t2 t1 t2

and safe_dest_type t =
  let** t = whd t in
  match t.hd with
  | Type u when List.is_empty t.args -> Context_.Monad.ret u
  | Evar _ ->
    let* u = Context_.new_univ in
    (try let+ () = instantiate_evar t (mkType u) in
      u
    (* TOTHINK: Should I catch everything? *)
    with _ -> fun ctx -> raise (TypeError (ctx, NotAType t)))
  | _ -> fun ctx -> raise (TypeError (ctx, NotAType t))

and typecheck t =
  let** _ = fun ctx -> assert (List.for_all (fun (_, (_, k, _)) -> 0 <= k) (IMap.to_list ctx.univ.levels)) in
  let timestamp = timestamp () in let _ = timestamp in
  let** debug = Context_.get_flag_opt "debug-unification" in
  let** () = if Option.is_some debug then let+* t = print t in print_endline (timestamp ^ ": typecheck " ^ t) else Context_.Monad.iret () in
  let ret = Context_.Monad.ret in
  let* ty = match t.hd with
    | Var i -> Context_.Monad.to_mut (Context_.get_var_type i)
    | Const (c, s, u) ->
      let** ty = Context_.get_const_type c in
      let ss = List.fold_left (fun ss (i, s) -> IMap.add i s ss) IMap.empty (List.mapi (fun i s -> (i, s)) s) in
      let su = List.fold_left (fun su (i, u) -> IMap.add i u su) IMap.empty ((0, Kernel.Univ.Level.of_var 0) :: List.mapi (fun i u -> (i + 1, u)) u) in
      let** ty = subst_univ ss su ty in
      ret ty
    | Type (s, u) -> ret (of_hd (Type (s, Kernel.Univ.Level.succ u)))
    | Fun (false, tele, body) ->
      Context_.fold_telescope (fun tele (v, ty, t, impl) ->
        let* tty = typecheck ty in
        let* _ = safe_dest_type tty in
        match t with
        | None -> ret ((v, ty, t, impl) :: tele)
        | Some t ->
          let* ty' = typecheck t in
          let* b = unify ~cumulative:Cumul ty' ty in
          if b then ret ((v, ty, Some t, impl) :: tele) else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) 
      ) [] tele (fun tele ->
        let+ ty = typecheck body in
        mkForall (List.rev tele) ty
      )
    | Fun (true, tele, body) ->
      Context_.fold_telescope (fun u (_, ty, t, _) ->
        let* v = typecheck ty in
        match t with
        | None ->
          let** v = whd v in
          let+ (_, v) = safe_dest_type v in
          Kernel.Univ.Level.max u v
        | Some t ->
          let* ty' = typecheck t in
          let* b = unify ~cumulative:Cumul ty' ty in
          if b then ret u else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) 
      ) Kernel.Univ.Level.base tele (fun u ->
        let* ty = typecheck body in
        let** ty = whd ty in
        let+ (s, v) = safe_dest_type ty in
        of_hd (Type (s, Kernel.Univ.Level.max u v))
      )
    | Ind (v, a, c) ->
      (* Check the arity *)
      let* tya = typecheck a in
      let** tya = whd tya in
      let* _ = safe_dest_type tya in
      (* Push the type of the inductive on the context *)
      Context_.with_var ~avoid_capture:false (v, a, None, false) (
      (* [check_positivity c] ensures that `c` contains only positive occurrences of the inductive being defined.
         returns true when the return type is the inductive type
         raises `Not_found` when there is a non positive occurrence *)
      (* strict = 
         0 : no occurence
         1 : strictly positive occurences
         2 : positive occurences *)
      let rec check_positivity ?(strict=2) ?(depth=0) t : bool Context_.Monad.it =
        let** t = whd t in
        match t.hd with
        | Var i when i = depth ->
          if strict = 0 then raise Not_found else
          let* () = Context_.Monad.List.fold_left (fun t () -> let** _ = check_positivity ~strict:0 ~depth t in ret ()) t.args () in
          Context_.Monad.iret true
        | Fun (true, tele, body) ->
          let strict' = if strict = 0 then 0 else strict-1 in
          Context_.Monad.to_imut (Context_.fold_telescope ~avoid_capture:false
            (fun depth (_, ty, t, _) ->
              if Option.is_some t then failwith "Letin is not supported in inductive definition." else 
              let** _ = check_positivity ~strict:strict' ~depth ty in
              ret (depth+1))
            depth tele
            (fun depth -> Context_.Monad.to_mut (check_positivity ~strict ~depth:depth body)))
        | _ -> let+* b = occurs (of_hd (Var depth)) t in if b then raise Not_found else false in
      let* () = List.fold_left (fun state c ->
        let* () = state in
        let* tyc = typecheck c in
        let** tyc = whd tyc in
        let* _ = safe_dest_type tyc in
        let** b = fun ctx -> try check_positivity c ctx with Not_found -> raise (TypeError (ctx, NonPositive c)) in
        if b then ret ()
        else fun ctx -> raise (TypeError (ctx, IllegalConstructorReturnType c))) (ret ()) c in
      ret a)
    | Construct (ind, i) ->
      (* Check ind is well-typed *)
      let* _ = typecheck ind in
      let** ind' = whd ind in
      let ind' = of_hd (ind'.hd) in
      let** _, _, c = fun ctx -> try destInd ind' with _ -> raise (TypeError (ctx, IllFormed t)) in
      if List.length c <= i then fun ctx -> raise (TypeError (ctx, IllFormed t)) else
      (* TODO: find a way to keep the folded version. *)
      ret (beta ind' (List.nth c i))
    | Case (ind', recursive) ->
      (* Check ind is well-typed *)
      let* _ = typecheck ind' in
      (* Get ind's content *)
      let** ind = whd ind' in
      let** (v, a, c) = fun ctx -> try destInd ind with _ -> raise (TypeError (ctx, IllFormed t)) in
      (* Get a's arity *)
      let* atele, asort = destArity a in
      let* asort = safe_dest_type asort in
      let na = List.length atele in
      let* runiv = Context_.new_univ in
      let* () = Context_.add_univ_constraint runiv asort in
      (* Build the predicate that gives the return type of the match... *)
      let rty = mkForall (atele @ [("_", mkApp (List.init na (fun i -> of_hd (Var (na-i-1)))) (bump na ind'), None, false)]) (of_hd (Type runiv)) in
      (* Start building the result's telescope, in reverse order *)
      let revtele = [("P", rty, None, false)] in
      (* The constructors expect the inductive type to be at position 0 in the context. *)
      Context_.with_var ~avoid_capture:false (v, a, None, false) (
      (* Transform the constructors into match branches and push them on the telscope
       ic : number of constructors already seen, every DeBruijn index should be bumped by ic before being pushed on the telescope.*)
      let** nc, revtele = List.fold_left (fun state c ->
        let** ic, revtele = state in
        let* ctele, cret = destArity ~whd_rty:true c in
        let nc = List.length ctele in
        (* Get the recursive calls telescope (if applicable) *)
        let* rec_calls =
          if not recursive then ret [] else
          Context_.fold_telescope
          (fun (iarg, rec_calls) (_, arg, t, _) ->
            if Option.is_some t then failwith "letin unsupported in constructor type" else
            let** { hd; args } = whd arg in
            ret (iarg+1,
              match hd with
              | Var i when i = iarg ->
                let args = List.map (bump (nc-iarg)) args in
                let args = args @ [of_hd (Var (nc-iarg-1))] in
                ("_", (mkApp args (of_hd (Var nc))), None, false) :: rec_calls
            | _ -> rec_calls))
          (0, []) ctele
          (fun (_, rec_calls) -> ret (List.rev rec_calls)) in
        (* We need to bump because there is the predicate between the arguments the constructors might refer to and the constructors themselves. *)
        let* ctele, cret = destArity (bump 1 (beta ind' (mkForall ctele cret))) in
        let ctele = ctele @ rec_calls in
        let arg = mkForall ctele (bump (List.length rec_calls) { hd = Var nc; args = (List.drop (List.length cret.args - na) cret.args) @ [{ hd = Construct (cret, ic); args = List.init nc (fun i -> of_hd (Var (nc-1-i))) }] }) in
        let arg = bump ic arg in
        Context_.Monad.iret (ic+1, ("_", arg, None, false) :: revtele)) (Context_.Monad.iret (0, revtele)) c in
      let revtele = ("_", mkApp (List.init na (fun i -> mkVar (na-i-1))) (bump (na+nc+1) ind'), None, false) :: (List.map (fun (v, ty, t, impl) -> (v, bump (nc+1) ty, t, impl)) (List.rev atele)) @ revtele in
      let tele = List.rev revtele in
      let ty = mkForall tele { hd = Var (na+nc+1); args = List.init (na+1) (fun i -> mkVar (na-i)) } in
      ret ty)
    | Evar i -> Context_.Monad.to_mut (Context_.get_evar_type i) in

(*   let** () = let+* ty = print ty in print_endline (timestamp ^ ": hdty = " ^ ty) in *)
(*   let** () = fun ctx -> print_endline ("ctx: " ^ String.concat "\n\t" (List.map (fun (i, (ty, t, _)) -> Int.print i ^ " -> " ^ print ty ctx ^ (match t with | None -> "" | Some t -> " := " ^ print t ctx) ) (IMap.to_list ctx.evar))) in *)

  let* _, ty = fun ctx ->
    try fold_left_args_with_type t.args ty (fun arg ty () ->
      let* tyarg = typecheck arg in
      let* b = unify ~cumulative:Cumul tyarg ty in
      if b then ret (arg, ()) else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, arg)))
    ) () ctx
    with TypeError (ctx, IllegalApplication _) -> raise (TypeError (ctx, IllegalApplication t)) in
  let** () = if Option.is_some debug then let+* ty = print ty in print_endline (timestamp ^ ": type is " ^ ty) else Context_.Monad.iret () in
  ret ty

(* For each occurrence of a problematic term in `t` (according to `pb`), performs as many beta-reductions, evar delta-reductions and evar instantiations as needed in the context surrounding the problematic term to make the latter disappear.
  This is used for instance to clear variables from the context, removing the occurrences of said variables from the term.
  `pb` is only given terms whose subterms are guaranteed to not be problematic.
  `pb` might called to subterms under binders, the context will tell how many. *)
and rm_problematic_term ?(instantiate_evars=false) pb t =
  let ret = Context_.Monad.ret in
  let lift_either b = function
    | Either.Left x -> x, b
    | Either.Right x -> x, false in
  let tag b = if b then Either.left else Either.right in
  let collapse_either = Either.fold ~left:(fun t -> t) ~right:(fun t -> t) in
  let fold_hd hd = match hd with
    | Var v -> Either.Left (mkVar v)
    | Const (c, s, u) -> Either.Left (mkConst c s u)
    | Type u -> Either.Left (mkType u)
    | Evar i -> Either.Left (of_hd (Evar i))
    | Fun (f, tele, body) ->
      let rtele, b = List.fold_left (fun (rtele, b) (v, ty, t, impl) ->
        let ty, b = lift_either b ty in
        let t, b = match t with | None -> None, b | Some (Either.Left t) -> Some t, b | Some (Either.Right t) -> Some t, false in
        (v, ty, t, impl) :: rtele, b
      ) ([], true) tele in
      let body, b = lift_either b body in
      tag b (of_hd (Fun (f, List.rev rtele, body)))
    | Ind (v, a, c) ->
      let a, b = lift_either true a in
      let rc, b = List.fold_left (fun (rc, b) c -> let c, b = lift_either b c in c :: rc, b) ([], b) c in
      tag b (of_hd (Ind (v, a, List.rev rc)))
    | Construct (ind, i) -> let ind, b = lift_either true ind in tag b (of_hd (Construct (ind, i)))
    | Case (ind, r) -> let ind, b = lift_either true ind in tag b (of_hd (Case (ind, r))) in
  let rec aux t =
    let* hd = Context_.Monad.Head.map aux t.hd in
    let* args = Context_.Monad.List.map aux t.args in
    fold_app hd args
  and fold_app hd args =
    let rhd = fold_hd hd in
    let** r =
      if List.exists Either.is_right args then Context_.Monad.iret None else
      match rhd with | Either.Right _ -> Context_.Monad.iret None | Either.Left hd ->
      let t = mkApp (List.map (Either.fold ~left:(fun t -> t) ~right:(fun _ -> failwith "unreachable")) args) hd in
      let+* b = pb t in
      if b then None else Some t in
    match r with | Some t -> Context_.Monad.ret (Either.Left t) | None ->
    (* Length of the longest prefix of args that ends in `Either.Right. *)
    let npb = List.length args - List.length (List.take_while Either.is_left (List.rev args)) in
    match hd with
    | Fun (false, tele, body) ->
      let ntele =
        if Either.is_right body then List.length tele else
        List.length tele - List.length (List.take_while (fun (_, ty, t, _) -> Either.is_left ty && Option.map_or true Either.is_left t) (List.rev tele)) in
      (* If no subterm is problematic, we still want to do a beta-reduction. *)
      let n = min (List.length tele) (max 1 (max npb ntele)) in
      let rhd = collapse_either rhd in
      (* If I need to reduce more than I have arguments, there will remain problematic terms after reduction. *)
      if List.length args < n then Context_.Monad.ret (Either.Right (mkApp (List.map collapse_either args) rhd)) else
      let tele, body = match rhd.hd with | Fun (_, tele, body) -> tele, body | _ -> failwith "unreachable" in
      let tele = List.drop n tele in
      let args, rest = List.split_at n args in
      let args = IMap.of_list (List.mapi (fun i t -> (i, collapse_either t)) (List.rev args)) in
      let t = subst (fun i -> try IMap.find i args with _ -> mkVar (i - n)) (mkFun tele body) in
      let* hd = Context_.Monad.Head.map aux t.hd in
      let* args = Context_.Monad.List.map aux t.args in
      fold_app hd (args @ rest)
    | Evar i ->
      let** t = Context_.get_evar_body i in
      (match t with
      | Some t ->
        (* TOTHINK: Do I want to reduce all the lambdas in `t` as usual? *)
        let* hd = Context_.Monad.Head.map aux t.hd in
        let* targs = Context_.Monad.List.map aux t.args in
        fold_app hd (targs @ args)
      | None ->
        if not instantiate_evars then ret (Either.Right { hd = Evar i; args = List.map collapse_either args }) else
        let sargs = ISet.of_list (List.fold_left (fun args (i, x) -> if Either.is_left x then args else i :: args) [] (List.mapi (fun i x -> (i, x)) args)) in
        if ISet.is_empty sargs then ret (Either.Right { hd = Evar i; args = List.map collapse_either args }) else
        let* _ = prune_evar sargs i in
        fold_app hd args)
    | _ ->
      let rhd = collapse_either rhd in
      ret (Either.Right (mkApp (List.map collapse_either args) rhd)) in
  let+ t = aux t in
  Either.fold ~left:Option.some ~right:(fun _ -> None) t

and prune_evar args ev =
(*   let () = print_endline ("prune_evar " ^ ISet.print args) in *)
  let** d' = Context_.depth in
  if ISet.is_empty args then Context_.Monad.ret (mkEvar ev) else
  let largs = Dynarray.create () in
  let compile k t ctx =
    let n = Dynarray.length largs in
    let d' = d' + n in
    let ctx, t' = rm_problematic_term ~instantiate_evars:true (fun t ->
      let+* d = Context_.depth in
      match t.hd with
      | Var v when d <= v -> raise (TypeError (ctx, UnboundVar (v - d)))
      | Var v when d - d' <= v ->
        Option.is_none (Dynarray.get largs (n - (v - (d - d')) - 1))
      | _ -> false
    ) t ctx in
    let t = Option.value ~default:t t' in
    ctx, subst (fun v ->
      if n <= v then raise (TypeError (ctx, UnboundVar (v - n))) else
      let v = n - v - 1 in
      match Dynarray.get largs v with
      | None -> raise (TypeError (ctx, UnboundVar (n - v - 1)))
      | Some v -> mkVar (k - v - 1)) t in
  let* ty = typecheck (of_hd (Evar ev)) in
  let k = ISet.max_elt args in
  let* (tele, ty) = destArity ~until:(Exact (k + 1)) ty in
  let rec loop rtele rargs k = function | [] -> let+ ty = compile k ty in rtele, rargs, ty | (v, ty, t, impl) :: tele ->
    let n = Dynarray.length largs in
    if ISet.mem n args then let () = Dynarray.add_last largs None in Context_.with_var (v, ty, t, impl) (loop rtele rargs k tele) else
    let* ty = compile k ty in
    let* t = Context_.Monad.Option.map (fun t -> compile k t) t in
    let () = Dynarray.add_last largs (Some k) in
    Context_.with_var (v, ty, t, impl) (loop ((v, ty, t, impl) :: rtele) (n :: rargs) (k + 1) tele) in
  let* (rtele, rargs, ty) = loop [] [] 0 tele in

  let ty = mkForall (List.rev rtele) ty in
  let* ev' = Context_.new_evar ~ty:(Some ty) ~with_ctx:false in
  let* b = Context_.with_telescope ~avoid_capture:false tele (unify { hd = Evar ev; args = List.rev (List.init (k + 1) mkVar) } (mkApp (List.map (fun i -> mkVar (k - i)) (List.rev rargs)) ev')) in
  if b then Context_.Monad.ret ev' else failwith "unreachable"

(* Complete reduction. *)
let rec eval t =
  let** t = whd t in
  let+* args = Context_.Monad.to_imut (Context_.Monad.List.map (fun t -> Context_.Monad.to_mut (eval t)) t.args) in
  { hd = t.hd; args }

let reducible t = let+* t = whd_opt t in Option.is_some t

(* finds a function `fun x1 ... xn => t'` such that `t =~= (fun x1 ... xn => t') pats` *)
let pattern pats t =
  let ret = Context_.Monad.ret in
  let* tys = Context_.Monad.List.map typecheck pats in
  let tys = List.mapi bump tys in
  let tys = List.map (fun ty -> ("_", ty, None, false)) tys in
  let* () = Context_.push_telescope ~avoid_capture:false tys in
  let pats' = List.map (bump (List.length pats)) (List.rev pats) in
  let t = bump (List.length pats) t in
  let eq_pat pat pat' =
    match pat.hd, pat'.hd with
    | Var v, Var v' -> (v = v')
    | Const (c, _, _), Const (c', _, _) -> (c = c')
    (* TODO: Do I want to be more precise? *)
    | Fun (f, _, _), Fun (f', _, _) -> (f = f')
    | Type _, Type _ | Ind (_, _, _), Ind (_, _, _) -> true
    | Construct (_, i), Construct (_, i') -> (i = i')
    | Case (_, r), Case (_, r') -> (r = r')
    (* TODO: Do I want to reduce? *)
    | Evar i, Evar i' -> (i = i')
    | _, _ -> false in
  let rec compile t =
    let** t = whd ~flags:whd_flags_none t in
    let rec try_pat i = function | [] -> ret None | pat :: pats ->
      if not (eq_pat pat t) then try_pat (i + 1) pats else
      let* b = unify pat t in
      if not b then try_pat (i + 1) pats else
      ret (Some (mkVar i)) in
    let* r = try_pat 0 pats' in
    match r with | Some r -> ret r | None ->
    let* hd = match t.hd with
    | Var _ | Const (_, _, _) | Type _ | Evar _ -> ret t.hd
    | Fun (f, tele, body) ->
      Context_.fold_telescope ~avoid_capture:false (fun rtele (v, ty, t, impl) ->
        let* ty = compile ty in
        let+ t = Context_.Monad.Option.map compile t in
        (v, ty, t, impl) :: rtele) [] tele (fun rtele ->
        let+ body = compile body in
        Fun (f, List.rev rtele, body))
    | Ind (v, a, c) ->
      let* a = compile a in
      let+ c = Context_.with_var ~avoid_capture:false (v, a, None, false) (Context_.Monad.List.map compile c) in
      Ind (v, a, c)
    | Construct (ind, i) ->
      let+ ind = compile ind in
      Construct (ind, i)
    | Case (ind, r) ->
      let+ ind = compile ind in
      Case (ind, r) in
    let+ args = Context_.Monad.List.map compile t.args in
    { hd; args } in
  let* t = compile t in
  let* _ = Context_.Monad.List.map (fun _ -> Context_.pop_var) (List.init (List.length tys) (fun i -> i)) in
  let t = mkFun tys t in
  let+ _ = typecheck t in
  mkApp pats t

let rec to_kernel t =
  let ret = Context_.Monad.ret in
  let open Kernel in
  Context_.Monad.to_imut (fold ~avoid_capture:false (function
    | Var i -> ret (Term.of_hd (Term.Var i))
    | Const (c, s, u) -> ret (Term.of_hd (Term.Const (c, s, u)))
    | Fun (f, tele, t) -> ret (Term.of_hd (Term.Fun (f, tele, t)))
    | Type s -> ret (Term.of_hd (Term.Type s))
    | Ind (v, a, c) -> ret (Term.of_hd (Term.Ind (v, a, c)))
    | Construct (ind, i) -> ret (Term.of_hd (Term.Construct (ind, i)))
    | Case (ind, r) -> ret (Term.of_hd (Term.Case (ind, r)))
    | Evar i ->
      let** t = Context_.get_evar_body i in
      (match t with | None -> fun ctx -> raise (TypeError (ctx, NoBody (of_hd (Evar i)))) | Some t ->
      Context_.Monad.to_mut (to_kernel t)))
  (function | [] -> failwith "unreachable" | hd :: args -> ret (Term.mkApp args hd)) t)

module Context = struct
  include Context_

  let term_to_kernel = to_kernel

  let to_kernel (ctx : t) =
    let ctx, var = Monad.List.map (fun (i, (v, ty, t, impl)) ->
      let** ty = term_to_kernel ty in
      let+ t = Monad.Option.map (fun t -> Monad.to_mut (term_to_kernel t)) t in
      (i, (v, ty, t, impl))) (IMap.to_list ctx.var) ctx in
    let var = IMap.of_list var in
    Kernel.Term.{ univ = ctx.univ; var; const = ctx.const }

  let push_const c (ty, t) =
    let** ty = term_to_kernel ty in
    let* t = Monad.Option.map (fun t -> Monad.to_mut (term_to_kernel t)) t in
    fun ctx ->
      let kctx, () = Kernel.Term.Context.push_const c (ty, t) (to_kernel ctx) in
      { ctx with univ = kctx.univ; const = kctx.const }, ()

  let get_hints = get_hints

  let print ?(debug=false) ctx =
    let ectx = { ctx with var = IMap.empty } in
    let kctx = to_kernel ectx in
    let (+) = String.cat in
    String.concat "\n" ([
      "CTX:\n\t Local variables:";

      snd (fold_telescope ~avoid_capture:true (fun s (v, ty, t, _) ->
      let** ty = print ~debug ty in
      let* t = Monad.Option.map (fun t -> Monad.to_mut (print ~debug t)) t in
      Monad.ret (s + "\t\t" + v + " : " + ty + (match t with | None -> "" | Some t -> " := " + t) + "\n")) "" (List.map snd (IMap.to_list ctx.var)) Monad.ret { ctx with var = IMap.empty });

      "\t Global variables:"] @

      List.map (fun (v, (_, ty, t)) -> "\t\t" + v + " : " + Kernel.Term.print ~debug ty kctx + (match t with | None -> "" | Some t -> " := " + Kernel.Term.print ~debug t kctx)) (SMap.to_list ctx.const) @

      ["\t Evars:"] @
      List.map (fun (i, (ty, t, cstrs)) ->
        "\t\t ?" + string_of_int i + " : " + print ~debug ty ectx + (match t with | None -> "" | Some t -> " := " + print ~debug t ectx) +
        String.concat "" (List.map (fun (var, l, r) -> let ctx = { ectx with var } in "\n\t\t\t" + print ~debug l ctx + " =~= " + print ~debug r ctx) cstrs)
      ) (IMap.to_list ctx.evar))

end
