open Utils

type 'a binder = string * 'a * 'a option * bool (* implicit *)
type 'a telescope = 'a binder list
type 'a arity = 'a telescope * 'a

type 'a head =
  | Var of int (* De Bruijn indices *)
  | Const of string * Univ.Sort.t list * Univ.Level.t list
  | Fun of bool (* true if forall *) * 'a telescope * 'a
  | Type of Univ.t
  | Ind of string * (* arity *) 'a * (* constructors *) 'a list
  | Construct of 'a * int
  | Case of (* inductive *) 'a * (* recursive *) bool

type term = { hd: term head; args: term list }
type t = term

let binder_to_json value_to_json (v, ty, t, impl) = `List [ String.to_json v; value_to_json ty; Option.to_json value_to_json t; Int.to_json (if impl then 1 else 0) ]

let head_to_json value_to_json = function
  | Var i -> `Assoc [ ("var", (Int.to_json i : Yojson.Basic.t)) ]
  | Const (s, u, v) -> `Assoc [ ("const", `List [String.to_json s; List.to_json Univ.Sort.to_json u; List.to_json Univ.Level.to_json v]) ]
  | Fun (f, tele, body) -> `Assoc [ ((if f then "forall" else "fun"), `List [ List.to_json (binder_to_json value_to_json) tele; value_to_json body ]) ]
  | Type (s, u) -> `Assoc [ ("type", `List [ Univ.Sort.to_json s; Univ.Level.to_json u ]) ]
  | Ind (v, a, c) -> `Assoc [ ("ind", `List [ String.to_json v; value_to_json a; List.to_json value_to_json c ]) ]
  | Construct (ind, i) -> `Assoc [ ("mk", `List [ value_to_json ind; Int.to_json i ]) ]
  | Case (ind, r) -> `Assoc [ ("match", `List [ value_to_json ind; Int.to_json (if r then 1 else 0) ]) ]

let binder_of_json value_of_json j = 
  match List.of_json (fun x -> x) j with
  | v :: ty :: t :: impl :: [] -> (String.of_json v, value_of_json ty, Option.of_json value_of_json t, Int.of_json impl = 1)
  | _ -> raise (Invalid_argument "head_of_json.tele")

let head_of_json value_of_json j =
  match List.hd (Yojson.Basic.Util.keys j) with
  | "var" -> Var (Int.of_json (Yojson.Basic.Util.member "var" j))
  | "const" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "const" j) with
    | s :: u :: v :: [] -> Const (String.of_json s, List.of_json Univ.Sort.of_json u, List.of_json Univ.Level.of_json v)
    | _ -> raise (Invalid_argument "head_of_json.const"))
  | ("forall" | "fun" ) as k ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member k j) with
    | tele :: body :: [] -> Fun (k = "forall", List.of_json (binder_of_json value_of_json) tele, value_of_json body)
    | _ -> raise (Invalid_argument ("head_of_json." ^ k)))
  | "type" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "type" j) with
    | s :: u :: [] -> Type (Univ.Sort.of_json s, Univ.Level.of_json u)
    | _ -> raise (Invalid_argument "head_of_json.type"))
  | "ind" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "ind" j) with
    | v :: a :: c :: [] -> Ind (String.of_json v, value_of_json a, List.of_json value_of_json c)
    | _ -> raise (Invalid_argument "head_of_json.ind"))
  | "mk" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "mk" j) with
    | ind :: i :: [] -> Construct (value_of_json ind, Int.of_json i)
    | _ -> raise (Invalid_argument "head_of_json.mk"))
  | "match" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "match" j) with
    | ind :: r :: [] -> Case (value_of_json ind, Int.of_json r = 1)
    | _ -> raise (Invalid_argument "head_of_json.match"))
  | _ -> raise (Invalid_argument "head_of_json")

let rec to_json t =
  `Assoc [ ("hd", head_to_json to_json t.hd); ("args", List.to_json to_json t.args) ]

let rec of_json j =
  { hd = head_of_json of_json (Yojson.Basic.Util.member "hd" j); args = List.of_json of_json (Yojson.Basic.Util.member "args" j) }

type context = {
  univ : Univ.Context.t;
  var : t binder IMap.t;
  const : (Univ.Context.t * t * t option) SMap.t
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
      | Case (ind, r) -> of_hd (Case (aux k ind, r))) in
  aux 0 t

(* [beta t t'] beta-reduces (\lambda. t') t *)
let beta t = subst (fun i -> if i = 0 then t else of_hd (Var (i-1)))

let is_ground t = try ignore (subst (fun _ -> raise Not_found) t); true with Not_found -> false

module Context_ = struct
  type t = context

  let empty = { univ = Univ.Context.empty; var = IMap.empty; const = SMap.empty }

  let depth ctx = match IMap.max_binding_opt ctx.var with | None -> 0 | Some (x, _) -> x + 1

  let push_var ?(avoid_capture=true) (v, ty, body, impl) ctx =
    let d = depth ctx in
    let v = if avoid_capture then Utils.fresh_name v (List.map (fun (_, (n, _, _, _)) -> n) (IMap.to_list ctx.var)) else v in
    { ctx with var = IMap.add d (v, ty, body, impl) ctx.var }

  module Monad = Utils.ContextMonad(struct type t = context end)

  open Monad.Notations

  let with_var ?(avoid_capture=true) v f ctx =
    let ctx' = push_var ~avoid_capture v ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var }, r)

  let fold_telescope ?(avoid_capture=true) f x tele k ctx =
    let ctx', r = List.fold_left (fun (ctx, x) (v, ty, t, impl) ->
      let (ctx, r) = f x (v, ty, t, impl) ctx in
      push_var ~avoid_capture (v, ty, t, impl) ctx, r) (ctx, x) tele in
    let ctx', r = k r ctx' in
    ({ ctx' with var = ctx.var }, r)

  let univ ctx = ctx.univ

  let find_var i ctx =
    try IMap.find (depth ctx - i - 1) ctx.var with _ -> raise (TypeError (ctx, UnboundVar i))

  let find_const c ctx =
    try SMap.find c ctx.const with _ -> raise (TypeError (ctx, UnboundConst c))

  let get_var_name i = let+* (v, _, _, _) = find_var i in v
  let get_var_type i = let+* (_, ty, _, _) = find_var i in bump (i + 1) ty
  let get_var_body i = let+* (_, _, t, _) = find_var i in Option.map (bump (i + 1)) t

  let var_depth = depth

  let get_const_univ c = let+* (u, _, _) = find_const c in u
  let get_const_type c = let+* (_, t, _) = find_const c in t
  let get_const_body c = let+* (_, _, b) = find_const c in b

  (* TODO: propagate names *)
  let new_univ ctx =
    let univ, u = Univ.Context.new_univ None None ctx.univ in
    { ctx with univ }, u

  let new_univs_with_constraints univs ctx =
    let univ, s = Univ.Context.append univs ctx.univ in
    { ctx with univ }, s

  let add_sort_constraint s1 s2 ctx =
    let univ, () = Univ.Context.add_sort_constraint s1 s2 ctx.univ in
    { ctx with univ }, ()

  let add_level_constraint u1 u2 ctx =
    let univ, () = Univ.Context.add_level_constraint u1 u2 ctx.univ in
    { ctx with univ }, ()

  let add_univ_constraint u u' ctx =
    let univ, () = Univ.Context.add_constraint u u' ctx.univ in
    { ctx with univ }, ()

  let push_telescope ?(avoid_capture=true) tele ctx =
    List.fold_left (fun ctx b -> push_var ~avoid_capture b ctx) ctx tele, ()

  let with_telescope ?(avoid_capture=true) tele f ctx =
    let ctx', () = push_telescope ~avoid_capture tele ctx in
    let (ctx', r) = f ctx' in
    ({ ctx' with var = ctx.var }, r)

  let pop_var ctx =
    if IMap.is_empty ctx.var then raise (TypeError (ctx, UnboundVar 0)) else
    { ctx with var = IMap.remove (fst (IMap.max_binding ctx.var)) ctx.var }, ()
end

open Context_.Monad.Notations

let rec fold ?(avoid_capture=true) fold_hd fold_app t =
  let fold = fold fold_hd fold_app in
  let* hd = match t.hd with
    | Var v -> Context_.Monad.ret (Var v)
    | Const (c, s, u) -> Context_.Monad.ret (Const (c, s, u))
    | Type u -> Context_.Monad.ret (Type u)
    | Fun (forall, tele, body) ->
        Context_.fold_telescope ~avoid_capture (fun tele (x, ty, body, impl) ->
          let* ty = fold ty in
          let+ body = Context_.Monad.Option.map fold body in
          ((x, ty, body, impl) :: tele)
        ) [] tele (fun tele -> 
          let+ body = fold body in
          (Fun (forall, List.rev tele, body))
        )
    | Ind (v, a, c) ->
      let* a' = fold a in
      let+ c = Context_.with_var ~avoid_capture (v, a, None, false) (Context_.Monad.List.map fold c) in
      Ind (v, a', c)
    | Construct (ind, i) ->
      let+ ind = fold ind in
      Construct (ind, i)
    | Case (ind, r) ->
      let+ ind = fold ind in
      Case (ind, r) in
  let* hd = fold_hd hd in
  let* args = Context_.Monad.List.map fold t.args in
  fold_app (hd :: args)

let print ?(debug=false) t =
  let (+) = String.cat in
  let ret = Context_.Monad.ret in
  let rec fold_hd = function
    | Var v -> if debug then ret ("_" + string_of_int v, true) else let** c = Context_.get_var_name v in ret (c, true)
    | Const (c, s, u) -> ret (c + "@{" + String.concat ", " (List.map Univ.Sort.print s) + ";" + String.concat ", " (List.map Univ.Level.print u) + "}", true)
    | Fun (forall, (v, ty, Some t, _) :: tele, body) -> let+ (body, _) = if List.is_empty tele then ret body else fold_hd (Fun (forall, tele, body)) in ("let " + v + " : " + (fst ty) + " := " + (fst t) + " in " + body, false)
    | Fun (forall, tele, body) -> ret ((if forall then "forall " else "fun ") + String.concat " " (List.map (fun (v, ty, t, impl) ->
          (if impl then "{" else "(") + v + " : " + fst ty + (match t with | None -> "" | Some t -> " := " + fst t) + (if impl then "}" else ")")
      ) tele) + (if forall then ", " else " => ") + fst body, false)
    | Type u -> ret (Univ.print u, true)
    | Ind (v, a, c) -> ret ("ind " + v + " : " + fst a + " :=" + " | " + String.concat " | " (List.map fst c), false)
    | Construct (ind, id) -> ret ("ind.mk(" + fst ind + ")." + string_of_int id, true)
    | Case (ind, recursive) -> ret ((if recursive then "ind.fix(" else "ind.case(") + fst ind + ")", true) in
  let+* (t, _) = Context_.Monad.to_imut (fold fold_hd
    (function
      | [hd] -> ret hd
      | args -> ret (String.concat " " (List.map (fun (t, atomic) -> if atomic then t else "(" + t + ")") args), false)) t) in
  t

let free_univs t =
  let (+) = fun (fs1, fu1) (fs2, fu2) -> (ISet.union fs1 fs2, ISet.union fu1 fu2) in
  let ret = Context_.Monad.ret in
  Context_.Monad.to_imut (fold (fun hd -> ret (match hd with
    | Var _ -> (ISet.empty, ISet.empty)
    | Type (s, u) -> (Univ.Sort.free_vars s, Univ.Level.free_vars u)
    | Const (_, s, u) -> List.fold_left ISet.union ISet.empty (List.map Univ.Sort.free_vars s), List.fold_left ISet.union ISet.empty (List.map Univ.Level.free_vars u)
    | Fun (_, tele, body) -> List.fold_left (+) body (List.map (fun (_, ty, t, _) -> match t with | None -> ty | Some t -> ty + t) tele)
    | Ind (_, a, c) -> List.fold_left (+) a c
    | Construct (ind, _) | Case (ind, _) -> ind))
    (fun args -> ret (List.fold_left (+) (ISet.empty, ISet.empty) args)) t)

(* Checks whether `t'` occurs in `t`. *)
let occurs t' t =
  let prefix t' t =
    if List.length t.args < List.length t'.args then false else
    let rec eq t t' =
      List.length t.args = List.length t'.args &&
      (match t.hd, t'.hd with
      | Var v, Var w -> v = w
      | Fun (f, t, b), Fun (f', t', b') -> f = f' &&
        List.length t = List.length t' &&
        List.for_all2 (fun (_, ty, t, _) (_, ty', t', _) -> eq ty ty' && Option.equal eq t t') t t' &&
        eq b b'
      | Type u, Type u' -> u = u'
      | Ind (_, a, c), Ind (_, a', c') -> eq a a' && List.for_all2 eq c c'
      | Construct (ind, i), Construct (ind', i') -> i = i' && eq ind ind'
      | Case (ind, r), Case (ind', r') -> r = r' && eq ind ind'
      | _, _ -> false) &&
      List.for_all2 eq t.args t'.args in
    eq { t with args = List.take (List.length t'.args) t.args } t' in
  let rec aux t' t =
    prefix t' t ||
    (match t.hd with
    | Var _ | Type _ | Const _ -> false
    | Fun (_, tele, body) ->
      let t' = List.fold_left (fun t' (_, ty, t, _) -> Option.bind t' (fun t' -> if List.exists (aux t') (ty :: Option.to_list t) then None else Some (bump 1 t'))) (Some t') tele in
      (match t' with | None -> true | Some t' -> aux t' body)
    | Ind (_, arity, constructors) ->
      aux t arity || List.exists (aux (bump 1 t')) constructors
    | Construct (ind, _) | Case (ind, _) -> aux t ind) ||
    List.exists (aux t') t.args in
  aux t' t

let subst_univ ss su t =
  Context_.Monad.to_imut (fold (fun t -> Context_.Monad.ret @@ of_hd (match t with
    | Const (c, s, u) -> Const (c, List.map (Univ.Sort.subst ss) s, List.map (Univ.Level.subst su) u)
    | Type (s, u) -> Type (Univ.Sort.subst ss s, Univ.Level.subst su u)
    | t -> t))
    (function | [] -> failwith "unreachable" | t :: args -> Context_.Monad.ret { hd = t.hd; args }) t)

(* TODO: find better names. *)
type until = | Max | Exact of int | AtMost of int
let until_take n = function
  | Max -> Max
  | Exact m -> Exact (m - n)
  | AtMost m -> AtMost (m - n)
let until_opt = function | Max -> None | Exact n | AtMost n -> Some n

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
  match t.hd with
  | Fun (false, [(_, _, None, _)], body) -> 
    (match List.rev body.args with
    | { hd = Var 0; args = [] } :: l when not (List.exists (occurs (of_hd (Var 0))) (of_hd body.hd :: l)) ->
      Some { hd = body.hd; args = List.rev l @ t.args }
    | _ -> None)
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
  let** (vind, a, c) = fun ctx -> try destInd (of_hd ind) with Not_found -> raise (TypeError (ctx, IllFormed (of_hd h))) in
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
    Context_.Monad.to_imut (Context_.with_var (vind, a, None, false) (
    let** ctele, _ = destArity (List.nth c i) in
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
  (* let _ = print_string "whd "; print t; print_string "\n" in *)
  let ret = Context_.Monad.iret in
  match t.hd with
  | Var i when flags.delta ->
    let** body = Context_.get_var_body i in
    (match body with
    | None -> ret None
    | Some body ->
    let t = mkApp t.args body in
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t)
  | Const (c, s, u) when flags.delta ->
    let** body = Context_.get_const_body c in
    (match body with
    | None -> ret None
    | Some body ->
    let ss = List.fold_left (fun ss (i, s) -> IMap.add i s ss) IMap.empty (List.mapi (fun i s -> (i, s)) s) in
    let su = List.fold_left (fun su (i, u) -> IMap.add i u su) IMap.empty ((0, Univ.Level.of_var 0) :: List.mapi (fun i u -> (i + 1, u)) u) in
    let** body = subst_univ ss su body in
    let t = mkApp t.args body in
    let+* t = if flags.once then ret t else whd ~flags t in

    Some t)
  (* Free normalization, preparing for eta reductions *)
  | Fun (false, tele, { hd = Fun (false, tele', body); args = [] }) ->
    let rec get_teles rteles = function
      | { hd = Fun (false, tele, body); args = [] } -> get_teles (tele :: rteles) body
      | t -> rteles, t in
    let rteles, body = get_teles [] body in
    whd_opt ~flags { hd = Fun (false, List.concat (tele :: tele' :: List.rev rteles), body); args = t.args }
  | Fun (f, (_, _, Some b, _) :: tele, body) when flags.zeta ->
    let t = mkApp t.args (beta b (mkForallOrFun f tele body)) in
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t
  | Fun (false, (_, _, None, _) :: tele, body) when flags.beta && not (List.is_empty t.args) ->
    (match t.args with | [] -> failwith "unreachable" | a :: args ->
    let t = mkApp args (beta a (mkFun tele body)) in
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t)
  | Fun (false, [(_, _, None, _)], _) when flags.eta ->
    (match eta t with
    | None -> ret None
    | Some t ->
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t)
  | Fun (false, ((_, _, None, _) as b) :: tele, body) when flags.eta ->
    let** t = Context_.Monad.to_imut (Context_.with_var ~avoid_capture:false b (Context_.Monad.to_mut (whd_opt ~flags:{ whd_flags_none with eta = true; once = flags.once } (mkFun tele body)))) in
    (match t with
    | None -> ret None
    | Some t ->
    let t = mkFun [b] t in
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t)
  | Case (_, _) when flags.iota ->
    let** t' = iota ~flags t in
    (match t' with
    | None -> ret None
    | Some t ->
    let+* t = if flags.once then ret t else whd ~flags t in
    Some t)
  | _ -> ret None

and whd ?(flags=whd_flags_all) t =
  let+* t' = whd_opt ~flags t in
  Option.value ~default:t t'

(* Splits `forall x1 ... xk, ty` into `[x1; ...; xn], forall x(n+1) ... xk, ty`. If `n` is None, takes the longest list possible. *)
and destArity ?(whd_rty=false) ?(keep_let=false) ?(until=Max) (t : t) : (t telescope * t) Context_.Monad.it =
  let ret = Context_.Monad.iret in
  if until_opt until = Some 0 then ret ([], t) else
  let** t' = whd t in
  match t'.hd with
  | Fun (true, tele, body) when keep_let ->
    let tele, rtele, until = match until_opt until with | None -> tele, [], Max | Some n -> let tele, rtele = List.split_at (min n (List.length tele)) tele in tele, rtele, until_take (List.length tele) until in 
    let body = mkForall rtele body in
    let* tele2, ty = Context_.with_telescope ~avoid_capture:false tele (Context_.Monad.to_mut (destArity ~whd_rty ~keep_let ~until body)) in
    ret (tele @ tele2, ty)
  | Fun (true, tele, body) ->
    let args = Dynarray.create () in
    let subst k =
      let n = Dynarray.length args in
      subst (fun i -> if n <= i then mkVar (i - k) else
        match Dynarray.get args (n - i - 1) with
        | Either.Left t -> t
        | Either.Right j -> mkVar (i + j - k)
      ) in
    let rec purge_lets until k acc tele =
      if until_opt until = Some 0 then (until, k, acc, tele) else
      match tele with
      | [] -> (until, k, acc, tele)
      | ((v, ty, None, impl) as b) :: tele ->
        let until = until_take 1 until in
        if k = 0 then purge_lets until k (b :: acc) tele else
        let b = (v, subst k ty, None, impl) in
        let () = Dynarray.add_last args (Either.Right k) in
        purge_lets until k (b :: acc) tele
      | ((_, _, Some t, _) :: tele) ->
        let () = Dynarray.add_last args (Either.Left t) in
        purge_lets until (k + 1) acc tele in
    let (until, k, tele, rest) = purge_lets until 0 [] tele in
    let tele = List.rev tele in
    let body = mkForall rest body in
    let body = if k = 0 then body else subst k body in
    if until_opt until = Some 0 then Context_.Monad.iret (tele, body) else
    let* tele2, ty = Context_.fold_telescope ~avoid_capture:false (fun () _ -> Context_.Monad.ret ()) () tele (fun () -> Context_.Monad.to_mut (destArity ~whd_rty ~keep_let ~until body)) in
    ret (tele @ tele2, ty)
  | _ -> if match until with | Exact _ -> false | _ -> true then ret ([], if whd_rty then t' else t) else raise Not_found

(* Complete reduction. *)
let rec eval t =
  let** t = whd t in
  let+* args = Context_.Monad.to_imut (Context_.Monad.List.map (fun t -> Context_.Monad.to_mut (eval t)) t.args) in
  { hd = t.hd; args }

let reducible t = let+* t = whd_opt t in Option.is_some t

type cumulativity = Conv | Cumul | Cocumul
let swap_cumulativity = function
  | Conv -> Conv
  | Cumul -> Cocumul
  | Cocumul -> Cumul

let rec unify ?(cumulative=Conv) t1 t2 =
  let ret = Context_.Monad.ret in

  (*let** () = let** t1 = print t1 in let+* t2 = print t2 in print_endline (t1 ^ (match cumulative with | Conv -> " =~= " | Cumul -> " <~= " | Cocumul -> " >~= ") ^ t2) in*)
  if t1 = t2 then ret true else

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
    | Var v, Var w -> ret (v = w)
    | Const (c, s, u), Const (c', s', u') ->
      ret (c = c') &&
      (if cumulative = Cocumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun s s' -> let+ () = Context_.add_sort_constraint s s' in true) s s' ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun s s' -> let+ () = Context_.add_sort_constraint s s' in true) s' s ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cocumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun u u' -> let+ () = Context_.add_level_constraint u u' in true) u u' ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try Context_.Monad.List.for_all2 (fun u u' -> let+ () = Context_.add_level_constraint u u' in true) u' u ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false))
    | Type u, Type u' -> 
      (if cumulative = Cocumul then ret true else (fun ctx -> try (let+ () = Context_.add_univ_constraint u u' in true) ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false)) &&
      (if cumulative = Cumul then ret true else (fun ctx -> try (let+ () = Context_.add_univ_constraint u' u in true) ctx with Univ.UnivError (univ, _) -> { ctx with univ }, false))
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
    ret (List.length t1.args = List.length t2.args) &&
    Context_.Monad.List.for_all2 unify t1.args t2.args in

  let whd t =
    let** t' = whd_opt ~flags:{ whd_flags_none with delta = true; once = true } t in
    let t, progress = match t' with | None -> t, false | Some t -> t, true in
    let+* t' = whd_opt ~flags:{ whd_flags_all with delta = false } t in
    let t, progress = match t' with | None -> t, progress | Some t -> t, true in
    if progress then Some t else None in

  rigid ~cumulative t1 t2 ||
  let** t2' = whd t2 in
  match t2' with
  | None ->
    let** t1 = whd t1 in
    (match t1 with
    | None -> ret false
    | Some t1 -> unify ~cumulative t1 t2)
  | Some t2 -> unify ~cumulative t1 t2

let rec fold_left_args_with_type args ty f acc =
  if List.is_empty args then Context_.Monad.ret (acc, ty) else
  let args' = Dynarray.create () in
  let subst t =
    let n = Dynarray.length args' in
    if n = 0 then t else subst (fun i -> if i < n then Dynarray.get args' (n - i - 1) else mkVar (i - n)) t in
  let** tele, ty = destArity ~whd_rty:false ~until:(AtMost (List.length args)) ty in
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

let rec typecheck t =
  (*let** () = let+* t = print t in print_endline ("typecheck " ^ t) in*)
  let ret = Context_.Monad.ret in
  let* ty = match t.hd with
    | Var i -> let** ty = Context_.get_var_type i in ret ty
    | Const (c, s, u) ->
      let** ty = Context_.get_const_type c in
      let ss = List.fold_left (fun ss (i, s) -> IMap.add i s ss) IMap.empty (List.mapi (fun i s -> (i, s)) s) in
      let su = List.fold_left (fun su (i, u) -> IMap.add i u su) IMap.empty ((0, Univ.Level.of_var 0) :: List.mapi (fun i u -> (i + 1, u)) u) in
      let** ty = subst_univ ss su ty in
      ret ty
    | Type (s, u) -> ret (of_hd (Type (s, Univ.Level.succ u)))
    | Fun (false, tele, body) ->
      Context_.fold_telescope (fun tele (v, ty, t, impl) ->
        let* _ = typecheck ty in
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
          let** (_, v) = fun ctx -> try destType v with _ -> raise (TypeError (ctx, NotAType ty)) in
          ret (Univ.Level.max u v)
        | Some t ->
          let* ty' = typecheck t in
          let* b = unify ~cumulative:Cumul ty' ty in
          if b then ret u else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) 
      ) Univ.Level.base tele (fun u ->
        let* ty = typecheck body in
        let** ty = whd ty in
        let** (s, v) = fun ctx -> try destType ty with _ -> raise (TypeError (ctx, NotAType body)) in
        ret (of_hd (Type (s, Univ.Level.max u v)))
      )
    | Ind (v, a, c) ->
      (* Check the arity *)
      let* tya = typecheck a in
      let** tya = whd tya in
      let** _ = fun ctx -> try destType tya with _ -> raise (TypeError (ctx, NotAType a)) in
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
        | _ -> if occurs (of_hd (Var depth)) t then raise Not_found else Context_.Monad.iret false in
      let* () = List.fold_left (fun state c ->
        let* () = state in
        let* tyc = typecheck c in
        let** tyc = whd tyc in
        let** _ = fun ctx -> try destType tyc with _ -> raise (TypeError (ctx, NotAType c)) in
        let** b = fun ctx -> try check_positivity c ctx with Not_found -> raise (TypeError (ctx, NonPositive c)) in
        if b then ret ()
        else fun ctx -> raise (TypeError (ctx, IllegalConstructorReturnType c))) (ret ()) c in
      ret a)
    | Construct (ind, i) ->
      (* Check ind is well-typed *)
      let* _ = typecheck ind in
      let** ind' = whd ind in
      let ind' = of_hd ind'.hd in
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
      let** atele, asort = destArity a in
      let** asort = fun ctx -> try destType asort with _ -> raise (TypeError (ctx, NotAType ind')) in
      let na = List.length atele in
      let* runiv = Context_.new_univ in
      let* () = Context_.add_univ_constraint runiv asort in
      (* Build the predicate that gives the return type of the match... *)
      let rty = mkForall (atele @ [("_", mkApp (List.init na (fun i -> of_hd (Var (na-i-1)))) (bump na ind'), None, false)]) (of_hd (Type runiv)) in
      (* Start building the result's telescope, in reverse order *)
      let revtele = [("_", rty, None, false)] in
      (* The constructors expect the inductive type to be at position 0 in the context. *)
      Context_.with_var ~avoid_capture:false (v, a, None, false) (
      (* Transform the constructors into match branches and push them on the telscope
       ic : number of constructors already seen, every DeBruijn index should be bumped by ic before being pushed on the telescope.*)
      let** nc, revtele = List.fold_left (fun state c ->
        let** ic, revtele = state in
        let** ctele, cret = destArity ~whd_rty:true c in
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
        let** ctele, cret = destArity (bump 1 (beta ind' (mkForall ctele cret))) in
        let ctele = ctele @ rec_calls in
        let arg = mkForall ctele (bump (List.length rec_calls) { hd = Var nc; args = (List.drop (List.length cret.args - na) cret.args) @ [{ hd = Construct (cret, ic); args = List.init nc (fun i -> of_hd (Var (nc-1-i))) }] }) in
        let arg = bump ic arg in
        Context_.Monad.iret (ic+1, ("_", arg, None, false) :: revtele)) (Context_.Monad.iret (0, revtele)) c in
      let revtele = ("_", mkApp (List.init na (fun i -> mkVar (na-i-1))) (bump (na+nc+1) ind'), None, false) :: (List.map (fun (v, ty, t, impl) -> (v, bump (nc+1) ty, t, impl)) (List.rev atele)) @ revtele in
      let tele = List.rev revtele in
      let ty = mkForall tele { hd = Var (na+nc+1); args = List.init (na+1) (fun i -> mkVar (na-i)) }in
      ret ty) in

  let* _, ty = fold_left_args_with_type t.args ty (fun arg ty () ->
    let* tyarg = typecheck arg in
    let* b = unify ~cumulative:Cumul tyarg ty in
    if b then ret (arg, ()) else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, arg)))
  ) () in
  ret ty

(*let rec check_univ_covariance ctx u t =
  let max_cov = function
  | Univ.Invariant, _ | _, Univ.Invariant -> Univ.Invariant
  | Univ.Irrelevant n, Univ.Irrelevant n' -> Univ.Irrelevant (max n n')
  | Univ.Irrelevant n, Univ.Covariant n' | Univ.Covariant n, Univ.Covariant n' | Univ.Covariant n, Univ.Irrelevant n' -> Univ.Covariant (max n n')
  | Univ.Irrelevant _, _ | _, Univ.Invariant -> cov'
  | Univ.Contravariant, Univ.Contravariant -> Univ.Contravariant
  | Univ.Contravariant, _ -> Univ.Invariant in
  match t with
  | Var v -> 
    (try check_univ_covariance ctx u (Context_.get_var_body ctx i2) with _ -> Univ.Irrelevant 0)
  | Const (u, c) ->
    List.fold_left2 (fun cov u' cov' ->
      if not (IMap.mem u u') then cov else max_cov cov cov'
      ) (Univ.Irrelevant 0) (Context_.get_const_univ ctx c) (Context_.get_const_univ_covariance ctx c)
  | Fun (tele, body) ->
    let cov = List.fold_left2 (fun cov (_, t) ->
      max_cov cov (match check_univ_covariance t with | Univ.Irrelevant -> Univ.Irrelevant | _ -> Univ.Invariant)
    ) (Univ.Irrelevant 0) tele in
    max_cov cov (check_univ_covariance t)
  | Pi (tele, body) ->
    let cov = List.fold_left2 (fun cov (_, t) ->
      max_cov cov (match check_univ_covariance t with | Univ.Irrelevant -> Univ.Irrelevant | _ -> Univ.Invariant)
    ) (Univ.Irrelevant 0) tele in
    max_cov cov (check_univ_covariance t)
*)

let print_type_error e ctx =
  let (+) = String.cat in
  match e with
  | UnboundVar i -> "Unbound variable " + string_of_int i + "\n"
  | UnboundConst v -> "Unbound constant " + v + "\n"
  | NotAType t -> print t ctx + " is not a type\n"
  | IllegalApplication t -> "Illegal application in " + print t ctx + "\n"
  | TypeMismatch (ty, t) ->
    print t ctx + " does not have type " + print ty ctx + "\n"
  | IllFormed t -> print t ctx + " is ill-formed\n"
  | NoBody t -> print t ctx + "has no body\n"
  | NotGround t -> print t ctx + "is not ground\n"
  | IllegalConstructorReturnType t -> "Constructor should return an element of the inductive type, but has type " + print t ctx + "\n"
  | NonPositive t -> "Constructor of type " + print t ctx + " is not positive\n"
  | PropElimination t -> "Cannot eliminate " + print t ctx + "outside of Prop\n"

module Context = struct
  include Context_

  let push_const c (ty, t) =
    let** univ = univ in
    if not (is_ground ty) then fun ctx -> raise (TypeError (ctx, NotGround ty)) else
    if not (List.for_all is_ground (Option.to_list t)) then fun ctx -> raise (TypeError (ctx, NotGround (Option.get t))) else
    let* () = match t with
      | None -> Monad.ret ()
      | Some t ->
      let* ty' = typecheck t in
      let* b = unify ~cumulative:Cumul ty' ty in
      if b then Monad.ret () else fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) in
    let (univ, (ss, su)) = Univ.Context.optimize univ in
    let** ty = subst_univ ss su ty in
    let* t = Monad.Option.map (fun t -> Monad.to_mut (subst_univ ss su t)) t in
    let** fs, fu = free_univs ty in
    let (univ, (ss, su)) = Univ.Context.keep_univs fs fu univ in
    let** ty = subst_univ ss su ty in
    let* t = Monad.Option.map (fun t -> Monad.to_mut (subst_univ ss su t)) t in
    fun ctx -> { ctx with const = SMap.add c (univ, ty, t) ctx.const }, ()

  let print ctx =
    let (+) = String.cat in
    String.concat "\n" ([
      "CTX:\n\t Local variables:";

      snd (fold_telescope ~avoid_capture:true (fun s (v, ty, t, _) ->
      let** ty = print ty in
      let* t = Monad.Option.map (fun t -> Monad.to_mut (print t)) t in
      Monad.ret (s + "\t\t" + v + " : " + ty + (match t with | None -> "" | Some t -> " := " + t) + "\n")) "" (List.map snd (IMap.to_list ctx.var)) Monad.ret { ctx with var = IMap.empty });

      "\t Global variables:"] @

      List.map (fun (v, (_, ty, t)) -> "\t\t" + v + " : " + print ty ctx + (match t with | None -> "" | Some t -> " := " + print t ctx)) (SMap.to_list ctx.const))

  let to_json ctx =
    SMap.to_json String.to_json (fun (u, ty, t) -> `Assoc [ ("univ", Univ.Context.to_json u); ("ty", to_json ty); ("body", Option.to_json to_json t) ]) ctx.const

  let of_json j =
    { empty with const = SMap.of_json Yojson.Basic.Util.to_string (fun j -> (Univ.Context.of_json (Yojson.Basic.Util.member "univ" j), of_json (Yojson.Basic.Util.member "ty" j), Option.of_json of_json (Yojson.Basic.Util.member "body" j))) j }
end

