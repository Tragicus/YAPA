open Utils

type 'a telescope = (string * 'a) list
type 'a arity = 'a telescope * 'a

type t =
  | Var of int (* De Bruijn indices *)
  | Const of Kernel.Univ.t list * string
  | Fun of t telescope * t
  | App of t list (* FIXME: slow *)
  | Type of Kernel.Univ.t
  | Pi of t telescope * t
  | Let of string * t * t * t
  | Ind of (* arity *) t * (* constructors *) t list
  | Construct of t * int
  | Case of (* inductive *) t * (* recursive *) bool
  | Evar of int * t array
type term = t

(* Invariant : depth = List.length var *)
type context = {
  depth : int;
  univ : Kernel.Univ.Context.t;
  var : (string option * t * t option) list;
  const : (Kernel.Univ.Context.t * t * t) SMap.t;
  evar : (bool array * t * t option) IMap.t
}

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

exception TypeError of context * type_error

let head = function
  | App (f :: _) -> f
  | t -> t

let destVar = function
  | Var v -> v
  | _ -> raise Not_found

let destConst = function
  | Const (u, c) -> (u, c)
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

let destEvar = function
  | Evar (i, ctx) -> (i, ctx)
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
  | Fun (tele, body) -> () ++ "(fun"; pr_telescope tele ++ " => " + body ++ ")"
  | Pi (tele, body) -> () ++ "(forall"; pr_telescope tele ++ ", " + body ++ ")"
  | Let (v, ty, t, body) -> () ++ "(let " ++ v ++ " : " + ty ++ " := " + t ++ " in " + body ++ ")"
  | Var v -> () ++ "Var "; print_int v
  | Const (us, v) -> () ++ "Const " ++ v ++ "@{"; Utils.print_with_sep ", " Kernel.Univ.print us ++ "}"
  | App (f :: a) ->
    let (+) = fun _ e -> () ++ "(" + e ++ ")" in
    () ++ "App " + f; List.iter (fun e -> () ++ " " + e) a
  | Type u ->
    if Kernel.Univ.isProp u then () ++ "Prop" else
    () ++ "Type@{"; Kernel.Univ.print u ++ "}"
  | Ind (arity, constructors) ->
    () ++ "ind" ++ " : " + arity ++ " :="; List.iter (fun t -> () ++ " | " + t) constructors
  | Construct (ind, id) ->
    () ++ "ind.mk(" + ind ++ ")."; print_int id
  | Case (ind, recursive) ->
    () ++ (if recursive then "ind.fix(" else "ind.case(") + ind ++ ")"
  | Evar (i, ctx) ->
      print_string "?"; print_int i; if Array.length ctx = 0 then () else (() ++ "@{"; Utils.print_with_sep ", " print (Array.to_list ctx) ++ "}")
  | _ -> raise (TypeError ({ depth = 0; univ = Kernel.Univ.Context.empty; var = []; const = SMap.empty; evar = IMap.empty }, IllFormed e))

(* Replaces t by \lambda^k. t, avoiding capture *)
let rec bump k t = if k = 0 then t else subst (fun i -> Var (i + k)) (fun i -> Kernel.Univ.of_atom i 0) t

(* Replaces every `Var i` in `t` by `fvar i`, avoiding capture and `Type u` with `Type (funiv u)`. *)
and subst fvar funiv t =
  let rec aux k t =
    match t with
    | Var i -> if i < k then t else bump k (fvar (i - k))
    | Const (u, c) -> Const (List.map (Kernel.Univ.subst funiv) u, c)
    | Type u ->
      Type (Kernel.Univ.subst funiv u)
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
    | Case (ind, r) -> Case (aux k ind, r)
    | Evar (i, ctx) -> Evar (i, Array.map (subst fvar funiv) ctx) in
  aux 0 t

(* [beta t t'] beta-reduces (\lambda. t') t *)
let beta t = subst (fun i -> if i = 0 then t else Var (i-1)) (fun i -> Kernel.Univ.of_atom i 0)

let is_ground t = try ignore (subst (fun _ -> raise Not_found) (fun i -> Kernel.Univ.of_atom i 0) t); true with Not_found -> false

let rec free_univs = function
  | Var _ -> ISet.empty
  | Type u -> Kernel.Univ.free_vars u
  | Const (u, _) -> List.fold_left ISet.union ISet.empty (List.map Kernel.Univ.free_vars u)
  | App l -> List.fold_left ISet.union ISet.empty (List.map free_univs l)
  | Fun (tele, body) | Pi (tele, body) ->
    List.fold_left ISet.union (free_univs body) (List.map (fun (_, t) -> free_univs t) tele)
  | Let (_, ty, t, body) ->
    ISet.union (ISet.union (free_univs ty) (free_univs t)) (free_univs body)
  | Ind (a, c) ->
    List.fold_left ISet.union (free_univs a) (List.map free_univs c)
  | Construct (ind, _) | Case (ind, _) -> free_univs ind
  | Evar (_, ctx) -> Array.fold_left (fun us t -> ISet.union us (free_univs t)) ISet.empty ctx

module Context = struct
  type t = context

  let empty = { depth = 0; univ = Kernel.Univ.Context.empty; var = []; const = SMap.empty; evar = IMap.empty }

  let push_var (v, ty, body) ctx = { ctx with depth = ctx.depth+1; var = (v, bump 1 ty, Option.map (bump 1) body) :: ctx.var }

  module Monad = struct
    (* mutable state: function that computes an object of type 'a, potentially modifying the context. *)
    type 'a t = context -> context * 'a
    (* immutable state: function that computes an object of type 'a without modifying the context. *)
    type 'a it = context -> 'a

    let ret x ctx = ctx, x
    let iret x _ = x

    let to_mut state ctx = ctx, state ctx
    let to_imut state ctx = snd (state ctx)

    (* [bind state f ctx] binds a mutable state [state], i.e. executes [state] on [ctx] and then [f] on the result.
     - [state] is a mutable state
     - [f] can produce either a mutable or immutable state.
     Beware that when [f] produces an immutable state, the modifications of the context introduced by [state] are lost at the end of [f].
     *)
    let bind state f ctx =
      let (ctx, x) = state ctx in
      f x ctx

    (* [ibind state f ctx] binds an immutable state [state], i.e. executes [state] on [ctx] and then [f] on the result.
     - [state] is an immutable state
     - [f] can produce either a mutable or immutable state
     *)
    let ibind state f ctx = f (state ctx) ctx

    let map (state : 'b t) (f : 'b -> 'a) : 'a t = fun ctx ->
      let (ctx, x) = state ctx in
      (ctx, f x)

    let imap (state : 'b it) (f : 'b -> 'a) : 'a it = fun ctx ->
      f (state ctx)

    module Notations = struct
      (* let* binds a mutable state *)
      let (let*) = bind
      (* let** binds an immutable state *)
      let (let**) = ibind
      let (let+) = map
      let (let+*) = imap
    end
    open Notations

    let with_var v f ctx =
      let ctx' = push_var v ctx in
      let (ctx', r) = f ctx' in
      ({ ctx' with depth = ctx.depth; var = ctx.var }, r)

    let fold_telescope f x tele k ctx =
      let ctx', r = List.fold_left (fun (ctx, x) (v, ty) ->
        let (ctx, r) = f x (v, ty) ctx in
        push_var (Some v, ty, None) ctx, r) (ctx, x) tele in
      let ctx', r = k r ctx' in
      ({ ctx' with depth = ctx.depth; var = ctx.var }, r)

    module List = struct
      let map (f : 'a -> 'b t) l : 'b list t = fun ctx ->
        let ctx, l = List.fold_left (fun (ctx, l) x -> let ctx, y = f x ctx in ctx, y :: l) (ctx, []) l in
        ctx, List.rev l

      let rec for_all f = function
        | [] -> ret true
        | x :: l ->
          let* b = f x in
          if b then for_all f l else ret b

      let for_all2 f l l' ctx = for_all (fun (x, y) -> f x y) (List.combine l l') ctx
    end
  end

  open Monad.Notations

  let depth ctx = ctx.depth

  let univ ctx = ctx.univ

  let find_var i ctx =
    try List.nth ctx.var i with _ -> raise (TypeError (ctx, UnboundVar i))

  let find_const c ctx =
    try SMap.find c ctx.const with _ -> raise (TypeError (ctx, UnboundConst c))

  let find_evar i ctx =
    try IMap.find i ctx.evar with _ -> raise (TypeError (ctx, UnboundEvar i))

  let get_var_name i =
    let** (v, _, _) = find_var i in
    Monad.iret (Option.value v ~default:("_" ^ string_of_int i))
  let get_var_type i = let** (_, ty, _) = find_var i in Monad.iret (bump i ty)
  let get_var_body i =
    let** (_, _, t) = find_var i in
    match t with
    | None -> fun ctx -> raise (TypeError (ctx, NoBody (Var i)))
    | Some body -> Monad.iret (bump i body)

  let var_depth = depth

  let get_const_univ c =
    let+* (u, _, _) = find_const c in u
  let get_const_type c =
    let+* (_, t, _) = find_const c in t
  let get_const_body c =
    let+* (_, _, b) = find_const c in b

  let get_evar_context i =
    let+* (s, _, _) = find_evar i in s
  let get_evar_type i =
    let+* (_, t, _) = find_evar i in t
  let get_evar_body i =
    let+* (_, _, b) = find_evar i in b

  let push_var (v, ty, body) ctx = { ctx with depth = ctx.depth+1; var = (v, bump 1 ty, Option.map (bump 1) body) :: ctx.var }

  let new_univ ctx =
    let univ, u = Kernel.Univ.Context.new_univ ctx.univ in
    { ctx with univ }, u

  let new_univs_with_constraints univs ctx =
    let univ, newu = Kernel.Univ.Context.push_ctx univs ctx.univ in
    { ctx with univ }, newu

  let add_univ_constraints univ ctx =
    let univ = Kernel.Univ.Context.add univ ctx.univ in
    let _ = Kernel.Univ.Context.satisfiable univ in
    { ctx with univ }, ()

  let add_univ_constraint u u' ctx =
    add_univ_constraints (Kernel.Univ.Context.normalize u u') ctx

  let push_const c (u, t, ty) ctx =
    if not (is_ground t) then raise (TypeError (ctx, NotGround t)) else
    { ctx with const = SMap.add c (u, t, ty) ctx.const }, ()

  let push_telescope tele ctx =
    List.fold_left (fun ctx (v, ty) -> push_var (Some v, ty, None) ctx) ctx tele, ()

  let pop_var ctx =
    match ctx.var with
    | [] -> raise (TypeError (ctx, UnboundVar 0))
    | _ :: var -> { ctx with depth = ctx.depth-1; var }, ()

  let new_type_evar ctx =
    let ctx, u = new_univ ctx in
    let n = try fst (Utils.IMap.max_binding ctx.evar) + 1 with Not_found -> 0 in
    { ctx with evar = Utils.IMap.add n (Array.make ctx.depth true, Type u, None) ctx.evar}, Evar (n, Array.init ctx.depth (fun i -> Var i))

  let new_evar ctx =
    let ctx, t = new_type_evar ctx in
    let n = try fst (Utils.IMap.max_binding ctx.evar) + 1 with Not_found -> 0 in
    { ctx with evar = Utils.IMap.add n (Array.make ctx.depth true, t, None) ctx.evar}, Evar (n, Array.init ctx.depth (fun i -> Var i))
    
  (* FIXME: Is this doing the correct side effect? *)
  let evar_disallow_vars i s ctx =
    let (is, _, _) = find_evar i ctx in
    Array.iteri (fun i b -> if b then () else is.(i) <- false) s 

  let print ctx =
    print_string "CTX:\n\t Local variables:\n";
    List.iteri (fun i (v, ty, t) -> print_string "\t\t"; print_string (Option.value v ~default:("_" ^ string_of_int i)); print_string " : "; print ty; (match t with | None -> () | Some t -> print_string " := "; print t); print_string "\n") ctx.var;
    print_string "\n\t Global variables:\n";
    SMap.iter (fun v (_, ty, body) -> print_string "\t\t"; print_string v; print_string " : "; print ty; print_string " := "; print body; print_string "\n") ctx.const;
    print_string "\n\t Evars:\n";
    IMap.iter (fun i (_, ty, body) ->
      print_string "\t\t";
      print_string "?"; print_int i;
      print_string " : "; print ty;
      (match body with None -> () | Some body -> (print_string " := "; print body));
      print_string "\n") ctx.evar;
    print_string "\n"
end

open Context.Monad.Notations

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
    | Evar (_, _) -> () (* FIXME: Maybe I could check if t can appear in t' at all. *)
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

(* [iota t ctx] iota-reduces `t`, i.e. turns `App (Case (App (ind :: indargs), r) :: ret :: branches @ [App (Construct (ind, i) :: sargs)]` into:
  - `App (List.nth branches i :: indargs @ sargs` if `r` is `false` (non-recursive match)
  - `App (List.nth branches i :: indargs @ sargs @ rargs` with `args` being recursive calls on the elements of `sargs` that are from the inductive type being matched against if `r` is `true` (recursive match) *)

let rec iota ?(flags=whd_flags_all) t : t Context.Monad.it =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  let h, args = destApp t in
  match destCase h with
  | exception Not_found -> Context.Monad.iret t
  | ind, recursive ->
  let** ind = whd ind in
  let ind, aargs = destApp ind in
  let** (a, c) = fun ctx -> try destInd ind with Not_found -> raise (TypeError (ctx, IllFormed h)) in
  let nc = List.length c in
  (* Getting the subject. *)
  (match Utils.split_list_at (1 + nc) args with
  | exception Not_found | _, [] -> Context.Monad.iret t
  | objs, subject :: eargs ->
  let** subject = whd ~flags:(if flags.iota_all then whd_flags_all else flags) subject in
  let ci, sargs = destApp subject in
  (match destConstruct ci with
  | exception Not_found -> Context.Monad.iret t
  | _, i ->
  let** rargs =
    if not recursive then Context.Monad.iret [] else
    Context.Monad.to_imut (Context.Monad.with_var (None, a, None) (
    let** ctele, _ = destArity (List.nth c i) in
    let* _, rargs = Context.Monad.fold_telescope (fun (iarg, rargs) (_, arg) ->
      let** arg = whd arg in
      Context.Monad.ret (iarg+1,
      let hd, args = destApp arg in
      match hd with
      | Var i when i = iarg ->
        let args = List.map
          (subst (fun i ->
            if i < iarg then List.nth sargs (iarg-1-i) else
            if i = iarg then ind else Var(i)) (fun i -> Kernel.Univ.of_atom i 0))
          args in
        (mkApp (Case (mkApp ind args, recursive)) (objs @ [List.nth sargs iarg])) :: rargs
      | _ -> rargs)) (0, []) ctele Context.Monad.ret in
    Context.Monad.ret (List.rev rargs))) in
  let targs = aargs @ sargs @ rargs @ eargs in
  Context.Monad.iret (mkApp (List.nth objs (1+i)) targs)))

and whd ?(flags=whd_flags_all) t =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  (* let _ = print_string "whd "; print t; print_string "\n" in *)
  match t with
  | Const (univs, c) when flags.delta ->
    let** u = Context.get_const_univ c in
    let** t = Context.get_const_body c in
    let u = try List.tl (IMap.bindings u) with _ -> [] in
    let u = List.fold_left (fun g (v, u) -> IMap.add v u g) IMap.empty (List.map2 (fun (v, _) u -> (v, u)) u univs) in
    let t = subst (fun i -> Var i) (fun i -> try IMap.find i u with _ -> Kernel.Univ.of_atom i 0) t in
    if flags.once then Context.Monad.iret t else whd ~flags t
  | Fun ([(_, _)], _) as t when flags.eta -> Context.Monad.iret (eta t)
  | Fun ((v, ty) :: tele, body) when flags.eta ->
    let* body = Context.Monad.with_var (Some v, ty, None) (Context.Monad.to_mut (whd ~flags:{ whd_flags_none with eta = true; once = flags.once } (mkFun tele body))) in
    let t = mkFun [(v, t)] body in
    Context.Monad.iret (if flags.once then t else eta t)
  | Let (_, _, t, body) when flags.zeta -> whd ~flags (beta t body)
  | App (f :: args) ->
    let** f = whd ~flags f in
    let t = mkApp f args in
    (match destApp t with
    | Fun (_ :: tele, body), x :: args when flags.beta ->
      let t = mkApp (beta x (mkFun tele body)) args in
      if flags.once then Context.Monad.iret t else whd ~flags t
    | Case (_, _), _ when flags.iota ->
      let** t' = iota ~flags t in
      if flags.once || t' = t then Context.Monad.iret t else whd ~flags t'
    | h, _ ->
      Context.Monad.iret (mkApp h args))
  | Evar (i, ctx) ->
    let** b = Context.get_evar_body i in
    (match b with | None -> Context.Monad.iret t | Some t ->
    let t = subst (fun i -> ctx.(i)) (fun i -> Kernel.Univ.of_atom i 0) t in
    whd ~flags t)
  | t -> Context.Monad.iret t

and destArity ?(whd_rty=false) t =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  let** t' = whd t in
  match t' with
  | Pi (tele, body) ->
    Context.Monad.to_imut (Context.Monad.fold_telescope (fun _ _ -> Context.Monad.ret ()) () tele (fun _ ->
    let** tele2, r = destArity body in
    Context.Monad.ret (tele @ tele2, r)))
  | t' -> Context.Monad.iret ([], if whd_rty then t' else t)

(* [type_of t] returns the type of [t], assuming that [t] is well-typed. In particular, no verification is performed besides those
  that are required to build the type of [t]. *)
let rec type_of t =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  (* let () = print_string "type_of "; print t; print_string "\n" in *)
  let type_telescope ?(get_sorts=false) tele k =
    Context.Monad.fold_telescope (fun tele (v, t) ->
      let* ty = type_of t in
      let** ty = whd ty in
      match ty with
      | Type s ->
        let ty = if get_sorts then Type s else ty in
        Context.Monad.ret ((v, ty) :: tele)
      | _ -> fun ctx -> raise (TypeError (ctx, NotAType t))) [] tele (fun tele -> k (List.rev tele)) in
  match t with
  | Var i -> Context.Monad.to_mut (Context.get_var_type i)
  | Const (u, c) ->
    let** uctx = Context.get_const_univ c in
    let nu = List.length u in
    let uctx = Kernel.Univ.Context.subst (fun i ->
      if 0 < i && i <= nu then List.nth u (i-1) else
      Kernel.Univ.of_atom i 0) uctx in
    let* () = Context.add_univ_constraints uctx in
    let** ty = Context.get_const_type c in
    Context.Monad.ret (subst (fun i -> Var i) (fun i -> if i = 0 then Kernel.Univ.static 0 else List.nth u (i-1)) ty)
  | Type l -> Context.Monad.ret (Type (Kernel.Univ.shift 1 l))
  | Fun (tele, body) -> let+ ty = type_of body in mkPi tele ty
  | Pi (tele, body) ->
    type_telescope ~get_sorts:true tele (fun tytele ->
    let sorts = List.map destType (List.map snd tytele) in
    let* j =
      let* ty = type_of body in
      let** ty = whd ty in fun ctx ->
      try ctx, destType ty with
      | Not_found -> raise (TypeError (ctx, NotAType body)) in
    (* TOTHINK: Do I really need to reverse the sorts list? *)
    Context.Monad.ret (Type (List.fold_left (fun j i -> Kernel.Univ.max i j) j (List.rev sorts))))
  | App (f :: a) ->
    List.fold_left (fun ty t ->
      let* ty = ty in
      let** ty = whd ty in
      match ty with
      | Pi (_ :: tele, body) ->
        let** ty = whd ~flags:({ whd_flags_none with beta = true }) (beta t (mkPi tele body)) in
        Context.Monad.ret ty
      | _ -> fun ctx -> raise (TypeError (ctx, IllegalApplication (App (f :: a))))) (type_of f) a
  | Let (v, ty, t, body) ->
    let* tbody = Context.Monad.with_var (Some v, ty, Some t) (type_of body) in
    Context.Monad.ret (beta ty tbody)
  | Ind (a, _) -> Context.Monad.ret a
  | Construct (ind, i) ->
    let** ind' = whd ind in
    let** _, c = fun ctx -> try destInd ind' with _ -> raise (TypeError (ctx, IllFormed t)) in
    if List.length c <= i then fun ctx -> raise (TypeError (ctx, IllFormed t)) else
    Context.Monad.ret (beta ind (List.nth c i))
  | Case (ind', recursive) ->
    (* Get ind's content *)
    let** ind = whd ind' in
    let ind, _ = destApp ind in
    let** (a, c) = fun ctx -> try destInd ind with _ -> raise (TypeError (ctx, IllFormed t)) in
    (* Get a's arity *)
    let** atele, asort = destArity a in
    let** asort = fun ctx -> try destType asort with _ -> raise (TypeError (ctx, NotAType ind')) in
    let na = List.length atele in
    let* runiv = Context.new_univ in
    let* () = Context.add_univ_constraint runiv asort in
    (* Build the predicate that gives the return type of the match... *)
    let rty = mkPi (atele @ [("_", mkApp ind' (List.init na (fun i -> Var (na-i-1))))]) (Type runiv) in
    (* Start building the result's telescope, in reverse order *)
    let revtele = [("_", rty)] in
    (* The constructors expect the inductive type to be at position 0 in the context. *)
    Context.Monad.with_var (None, a, None) (
    (* Transform the constructors into match branches and push them on the telscope
     ic : number of constructors already seen, every DeBruijn index should be bumped by ic before being pushed on the telescope.*)
    let** nc, revtele = List.fold_left (fun state c ->
      let** ic, revtele = state in
      let** ctele, cret = destArity ~whd_rty:true c in
      let nc = List.length ctele in
      (* Get the recursive calls telescope (if applicable) *)
      let* rec_calls =
        if not recursive then Context.Monad.ret [] else
        Context.Monad.fold_telescope
        (fun (iarg, rec_calls) (_, arg) ->
          let** arg = whd arg in
          let hd, args = destApp arg in
          Context.Monad.ret (iarg+1,
            match hd with
            | Var i when i = iarg ->
              let args = List.map (bump (nc-iarg)) args in
              let args = args @ [Var (nc-iarg-1)] in
              ("_", (mkApp (Var nc) args)) :: rec_calls
          | _ -> rec_calls))
        (0, []) ctele
        (fun (_, rec_calls) -> Context.Monad.ret (List.rev rec_calls)) in
      (* We need to bump because there is the predicate between the arguments the constructors might refer to and the constructors themselves. *)
      let ctele, cret = destPi (bump 1 (beta ind' (mkPi ctele cret))) in
      let ctele = ctele @ rec_calls in
      let _, cargs = destApp cret in
      let arg = mkPi ctele (bump (List.length rec_calls) (mkApp (Var nc) (cargs @ [mkApp (Construct (cret, ic)) (List.init nc (fun i -> Var (nc-1-i)))]))) in
      let arg = bump ic arg in
      Context.Monad.iret (ic+1, ("_", arg) :: revtele)) (Context.Monad.iret (0, revtele)) c in
    let revtele = ("_", mkApp (bump (na+nc+1) ind') (List.init na (fun i -> Var (na-i-1)))) :: revtele in
    let tele = List.rev revtele in
    let ty = mkPi tele (mkApp (Var (na+nc+1)) (List.init (na+1) (fun i -> Var (na-i)))) in
    Context.Monad.ret ty)

  | Evar (i, _) -> Context.Monad.to_mut (Context.get_evar_type i)

  | _ -> fun ctx -> raise (TypeError (ctx, IllFormed t))

(* [instantiate_evar ev t] asserts that [ev] is of the form [(Evar i ictx) args] and defines the body of evar [i] with [t], capturing the subterms of [t] that appear in [args] or in [ictx].
    Heuristc: When there are several ways to capture subterms, we capture the largests first and then from the last argument to the first argument and then from the last element of the context to the first. *)
  let instantiate_evar ev t =
    let* () = Context.Monad.ret () in
    let (ev, args) = destApp ev in
    let (i, ictx) = destEvar ev in
    let** (is, ity, ibody) = Context.find_evar i in
    if ibody <> None then failwith "Anomaly: instanciating already instantiated evar." else
    let nargs = List.length args in
    let nctx = Array.length ictx in
    let subst = Array.make (nctx + nargs) None in
    let () = List.iteri (fun i t -> subst.(nargs - i - 1) <- Some t) args in
    let () = Array.iteri (fun i (b, t) -> subst.(nctx + nargs - i - 1) <- if b then Some t else None) (Array.combine is ictx) in
    let subst = Array.combine (Array.init (Array.length subst) (fun i -> i)) subst in
    let under_binder f =
      let () = Array.iter (fun (i, t) -> subst.(i) <- (i, Option.map (bump 1) t)) subst in
      let+ r = f in
      let () = Array.iter (fun (i, t) -> subst.(i) <- (i, Option.map (bump (-1)) t)) subst in
      r in
    let rec fold t =
      let** () = Context.Monad.iret () in (* Prevent reducing too early *)
      let i = Array.fold_left (fun i (j, t2) ->
        match i with | Some _ -> i | None ->
        if t2 = Some t then Some j else None) None subst in
      match i with Some i -> Context.Monad.ret (Option.get (snd subst.(i))) | None ->
      match t with
      | Var _ -> raise Not_found (* We should capture all variables *)
      | Const _ | Type _ -> Context.Monad.ret t (* FIXME: Should I introduce new universes? *)
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
      | Ind (ind, c) ->
        let* ind = fold ind in (fun ctx ->
        let ctx, c = List.fold_left_map (fun ctx t -> fold t ctx) ctx c in
        ctx, Ind (ind, c))
      | Construct (ind, i) -> let+ ind = fold ind in Construct (ind, i)
      | Case (ind, r) -> let+ ind = fold ind in Case (ind, r)
      | Evar (j, jctx) ->
        (* FIXME: Do I get the right side-effect on js? *)
        let** js = Context.get_evar_context j in
        let js = Array.copy js in
        let+ jctx = fun ctx -> Array.fold_left_map (fun ctx (i, t) ->
          if not js.(i) then ctx, t else
          try fold t ctx
          with Not_found -> let () = js.(i) <- false in ctx, t) ctx (Array.combine (Array.init (Array.length jctx) (fun i -> i)) jctx) in
        Evar (j, jctx) in
    let* t = fold t in
    let** t =
      let n = List.length args in
      if n = 0 then Context.Monad.iret t else
      let+* tele, _ = destArity ity in
      let tele, _ = split_list_at n tele in
      mkFun tele t in
    fun ctx -> { ctx with evar = IMap.add i (is, ity, Some t) ctx.evar }, ()

(* Complete reduction. *)
let rec eval t =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  match t with
  | Const (_, c) ->
    let** body = Context.get_const_body c in
    (match body with
    | exception Not_found -> Context.Monad.iret t
    | t -> eval t)
  | Fun ([(_, _)], _) as t -> Context.Monad.iret (eta t)
  | Fun ((v, ty) :: tele, body) ->
    let* body = Context.Monad.with_var (Some v, ty, None) (Context.Monad.to_mut (eval (mkFun tele body))) in
    Context.Monad.iret (eta (mkFun [(v, t)] body))
  | Let (_, _, t, body) -> eval (beta t body)
  | App l ->
    let* l = Context.Monad.List.map (fun x -> Context.Monad.to_mut (eval x)) l in
    (match l with
    | Fun (_ :: tele, body) :: x :: args ->
      let t = mkApp (beta x (mkFun tele body)) args in
      eval t
    | Case (_, _) :: _ ->
      let** t' = iota t in
      if t' = t then Context.Monad.iret t else eval t'
    | l -> Context.Monad.iret (App l))
  | Evar (i, ctx) ->
      let** b = Context.get_evar_body i in
      (match b with | None -> Context.Monad.iret t | Some t ->
      let t = subst (fun i -> ctx.(i)) (fun i -> Kernel.Univ.of_atom i 0) t in
      eval t)
  | t -> Context.Monad.iret t

let reducible t =
  let h, args = destApp t in
  match h with
  | Type _ | Pi _ | Ind _ | Construct _ -> Context.Monad.iret false
  | Fun _ -> Context.Monad.iret (args <> [])
  | Case (ind, _) ->
    let** ind = whd ind in
    let ind, _ = destApp ind in
    let** (_, c) = fun ctx -> try destInd ind with Not_found -> raise (TypeError (ctx, IllFormed ind)) in
    let nc = List.length c in
    if List.length args <= 1 + nc then Context.Monad.iret false else
    let** arg = whd (List.nth args (1 + nc)) in
    (Context.Monad.iret (match destApp arg with
    | Construct _, _ -> true
    | _, _ -> false))
  | Var i -> (fun ctx -> try let _ = Context.get_var_body i ctx in true with TypeError (_, NoBody _) -> false)
  | Const _ | Let _ -> Context.Monad.iret true
  | Evar (i, _) -> 
    let** b = Context.get_evar_body i in
    Context.Monad.iret (b <> None)
  | _ -> failwith "Internal error : head should not by an application."

type cumulativity = Conv | Cumul | Cocumul
let swap_cumulativity = function
  | Conv -> Conv
  | Cumul -> Cocumul
  | Cocumul -> Cumul

let rec unify ?(cumulative=Conv) t1 t2 =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  let (&&) state f =
    let* b = state in
    if not b then Context.Monad.ret b else
    f in
  let (||) state f =
    let* b = state in
    if b then Context.Monad.ret b else
    f in
  let unify_fun ?(builder=mkFun) (tele1, body1) (tele2, body2) =
    let l = min (List.length tele1) (List.length tele2) in
    let tele1, etele1 = Utils.split_list_at l tele1 in
    let tele2, etele2 = Utils.split_list_at l tele2 in
    Context.Monad.fold_telescope (fun (b, tele2) (_, ty1) ->
      if not b then Context.Monad.ret (b, tele2) else
      match tele2 with
      | [] -> (* FIXME: Should I fail harder? *) Context.Monad.ret (false, tele2)
      | (_, ty2) :: tele2 ->
        let+ b = unify ty1 ty2 in (b, tele2)
      ) (true, tele2) tele1 (fun (b, _) ->
      Context.Monad.ret b &&
      unify ~cumulative (builder etele1 body1) (builder etele2 body2)) in

  (* unifies t1 and t2 when t1 is an evar *)
  let rec evar ?(cumulative=Conv) (h1, args1 as t1) (h2, args2 as t2) ctx =
    let i, ictx = destEvar h1 in
    match h2 with
    | Evar (j, jctx) when i = j ->
      let is = Context.get_evar_context i ctx in
      let s = Array.make (Array.length ictx) true in
      let ctx = Array.fold_left (fun ctx (i, (t1, t2)) ->
        if not is.(i) then ctx else
        let ctx, b = unify t1 t2 ctx in
        let () = if b then () else s.(i) <- false in
        ctx) ctx (Array.combine (Array.init (Array.length ictx) (fun i -> i)) (Array.combine ictx jctx)) in
      let () = Context.evar_disallow_vars i s ctx in
      ctx, true
    | Evar (j, _) when Stdlib.(i < j && Context.get_evar_body j ctx = None) -> evar ~cumulative t2 t1 ctx
    | _ -> try let ctx, () = instantiate_evar (mkApp h1 args1) (mkApp h2 args2) ctx in ctx, true with Not_found -> ctx, false in

  (* unifies t1 and t2 when t2 is reducible *)
  let rec mixed ?(cumulative=Conv) (h1, args1 as t1) (h2, args2) =
    match h1, h2 with
    | _, Fun (tele2, body2) ->
      (match h1 with
      | Fun (tele1, body1) ->
        unify_fun (tele1, body1) (tele2, body2) &&
        Context.Monad.List.for_all2 unify args1 args2
      | _ -> Context.Monad.ret false) ||
      let** t2 = whd ~flags:{ whd_flags_none with beta = true; once = true } (mkApp h2 args2) in
      aux ~cumulative t1 (destApp t2)

    | _, Let (_, ty2, t2, body2) ->
      (match h1 with
      | Let (v, ty1, t1, body1) ->
        unify ty1 ty2 && unify t1 t2 && Context.Monad.with_var (Some v, ty1, None) (unify ~cumulative (mkApp body1 args1) (mkApp body2 args2))
      | _ -> Context.Monad.ret false) ||
      let** t2 = whd ~flags:{ whd_flags_none with zeta = true; once = true } (mkApp h2 args2) in
      aux ~cumulative t1 (destApp t2)

    | _, Var i2 ->
      (match h1 with
      | Var i1 when i1 = i2 -> Context.Monad.List.for_all2 unify args1 args2
      | _ -> Context.Monad.ret false) ||
      let** t2 = Context.get_var_body i2 in
      aux ~cumulative t1 (destApp (mkApp t2 args2))

    | _, Const (u2, c2) ->
      (match h1 with
      | Const (u1, c1) when c1 = c2 ->
        Context.Monad.ret (List.length args1 = List.length args2) && (
        Context.Monad.List.for_all2 (fun u u' ctx ->
          try
            (let* () = Context.add_univ_constraint u u' in
            let+ () = Context.add_univ_constraint u' u in true) ctx
          with _ -> ctx, false) u1 u2) &&
        Context.Monad.List.for_all2 unify args1 args2
      | _ -> Context.Monad.ret false) ||
      let** t2 = Context.get_const_body c2 in
      aux ~cumulative t1 (destApp (mkApp t2 args2))

    | _, Case (ind2, recursive2) ->
      (match h1 with
      | Case (ind1, recursive1) when recursive1 = recursive2 -> unify ind1 ind2 && Context.Monad.List.for_all2 unify args1 args2
      | _ -> Context.Monad.ret false) ||
      let** t2 = whd ~flags:{ whd_flags_none with iota = true; once = true } (mkApp h2 args2) in
      aux ~cumulative t1 (destApp t2)

    | _, Evar (i, ictx) ->
      (match h1 with
      | Evar (j, jctx) when i = j -> Context.Monad.List.for_all2 unify (Array.to_list ictx) (Array.to_list jctx) && Context.Monad.List.for_all2 unify args1 args2
      | _ -> Context.Monad.ret false) ||
      let** b = Context.get_evar_body i in
      (match b with | None -> Context.Monad.ret false (* FIXME: Should I fail? *) | Some t ->
      let t = subst (fun i -> ictx.(i)) (fun i -> Kernel.Univ.of_atom i 0) t in
      aux ~cumulative t1 (destApp (mkApp t args2)))

    | _, _ -> failwith "Internal error : non-reducible term classified as maybe reducible."

  and aux ?(cumulative=Conv) (h1, args1 as t1) (h2, args2 as t2) =
    (* Block reduction until we get the context. *)
    let** () = Context.Monad.iret () in
    (* let () = print_string "unify "; print (mkApp h1 args1); print_string "\n  and "; print (mkApp h2 args2); print_string "\n\n" in *)
    let** b = fun ctx -> match h1 with | Evar (i, _) -> Context.get_evar_body i ctx = None | _ -> false in
    if b then evar ~cumulative t1 t2 else
    let** b = fun ctx -> match h2 with | Evar (i, _) -> Context.get_evar_body i ctx = None | _ -> false in
    if b then evar ~cumulative t2 t1 else
    let** b = reducible (mkApp h2 args2) in
    if b then mixed ~cumulative t1 t2 else
    let** b = reducible (mkApp h1 args1) in
    if b then mixed ~cumulative t2 t1 else
    match h1, h2 with
    | Var i, Var j -> Context.Monad.ret (i = j) && Context.Monad.List.for_all2 unify args1 args2
    | Type u, Type u' -> (fun ctx -> try
        match cumulative with
        | Cumul -> 
          (let+ () = Context.add_univ_constraint u u' in true) ctx
        | Cocumul -> 
          (let+ () = Context.add_univ_constraint u' u in true) ctx
        | Conv ->
          (let* () = Context.add_univ_constraint u u' in
          let+ () = Context.add_univ_constraint u u' in true) ctx
      with _ -> ctx, false)
    | Fun (tele1, body1), Fun (tele2, body2)
    | Pi (tele1, body1), Pi (tele2, body2) ->
      unify_fun ~builder:mkPi (tele1, body1) (tele2, body2) && Context.Monad.List.for_all2 unify args1 args2
    | Ind (a1, c1), Ind (a2, c2) -> unify a1 a2 &&
      Context.Monad.with_var (None, a1, None) (Context.Monad.List.for_all2 unify c1 c2)
    | Construct (ind1, i1), Construct (ind2, i2) -> Context.Monad.ret (i1 = i2) && unify ind1 ind2
    | Case (ind1, r1), Case (ind2, r2) -> Context.Monad.ret (r1 = r2) && unify ind1 ind2
    | _, _ -> Context.Monad.ret false in
  aux ~cumulative (destApp t1) (destApp t2)

let rec typecheck t =
  (* Block reduction until we get the context. *)
  let** () = Context.Monad.iret () in
  (* let () = print_string "typecheck "; print t; print_string "\n" in *)
  let type_telescope ?(get_sorts=false) tele k =
    Context.Monad.fold_telescope (fun tele (v, t) ->
      let* ty = typecheck t in
      let** ty = whd ty in
      match ty with
      | Type s ->
        let ty = if get_sorts then Type s else ty in
        Context.Monad.ret ((v, ty) :: tele)
      | _ -> fun ctx -> raise (TypeError (ctx, NotAType t))) [] tele (fun tele -> k (List.rev tele)) in
  match t with
  | Var i -> Context.Monad.to_mut (Context.get_var_type i)
  | Const (_, _) -> type_of t
  | Type l -> Context.Monad.ret (Type (Kernel.Univ.shift 1 l))
  | Fun (tele, body) ->
    type_telescope tele (fun _ -> let* ty = typecheck body in Context.Monad.ret (mkPi tele ty))
  | Pi (tele, body) ->
    type_telescope ~get_sorts:true tele (fun tytele ->
    let sorts = List.map destType (List.map snd tytele) in
    let* j =
      let* ty = typecheck body in
      let** ty = whd ty in fun ctx ->
      try ctx, destType ty with
      | Not_found -> raise (TypeError (ctx, NotAType body)) in
    (* TOTHINK: Do I really need to reverse the sorts list? *)
    Context.Monad.ret (Type (List.fold_left (fun j i -> Kernel.Univ.max i j) j (List.rev sorts))))
  | App (f :: a) ->
    List.fold_left (fun ty t ->
      let* ty = ty in
      let** ty = whd ty in
      match ty with
      | Pi ([], body) -> Context.Monad.ret body
      | Pi ((_, ty) :: tele, body) ->
        let* tyt = typecheck t in
        let* b = unify ~cumulative:Cumul tyt ty in
        if not b then fun ctx -> raise (TypeError (ctx, TypeMismatch (ty, t))) else
        let** ty = whd ~flags:({ whd_flags_none with beta = true }) (beta t (mkPi tele body)) in
        Context.Monad.ret ty
      | _ -> fun ctx -> raise (TypeError (ctx, IllegalApplication (App (f :: a))))) (typecheck f) a
  | Let (v, ty, t, body) ->
    let* tbody = Context.Monad.with_var (Some v, ty, Some t) (typecheck body) in
    Context.Monad.ret (beta ty tbody)
  | Ind (a, c) ->
    (* Check the arity *)
    let* tya = typecheck a in
    let** tya = whd tya in
    let** _ = fun ctx -> match tya with
      | Type _ -> ()
      | _ -> raise (TypeError (ctx, NotAType a)) in
    (* Push the type of the inductive on the context *)
    Context.Monad.with_var (None, a, None) (
    (* [check_positivity c] ensures that `c` contains only positive occurrences of the inductive being defined.
       returns true when the return type is the inductive type
       raises `Not_found` when there is a non positive occurrence *)
    (* strict = 
       0 : no occurence
       1 : strictly positive occurences
       2 : positive occurences *)
    let rec check_positivity ?(strict=2) ?(depth=0) t : bool Context.Monad.it =
      let** t = whd t in
      match t with
      | Var i -> if i = depth && strict = 0 then raise Not_found else Context.Monad.iret true
      | App ((Var i) :: args) when i = depth ->
        if strict = 0 then raise Not_found else
        let** () = fun ctx -> List.iter (fun t -> ignore (check_positivity ~strict:0 ~depth t ctx)) args in
        Context.Monad.iret true
      | Pi (tele, body) ->
        let strict' = if strict = 0 then 0 else strict-1 in
        Context.Monad.to_imut (Context.Monad.fold_telescope
          (fun depth (_, t) ->
            let** _ = check_positivity ~strict:strict' ~depth t in
            Context.Monad.ret (depth+1))
          depth tele
          (fun depth -> Context.Monad.to_mut (check_positivity ~strict ~depth:depth body)))
      | t -> if occurs (Var depth) t then raise Not_found else Context.Monad.iret false in
    let* () = List.fold_left (fun state c ->
      let* () = state in
      let* tyc = typecheck c in
      let** tyc = whd tyc in
      let** _ = match tyc with Type _ -> Context.Monad.iret () | _ -> fun ctx -> raise (TypeError (ctx, NotAType c)) in
      let** b = fun ctx -> try check_positivity c ctx with Not_found -> raise (TypeError (ctx, NonPositive c)) in
      if b then Context.Monad.ret ()
      else fun ctx -> raise (TypeError (ctx, IllegalConstructorReturnType c))) (Context.Monad.ret ()) c in
    Context.Monad.ret a)
  | Construct (ind, _) ->
    (* Check ind is well-typed *)
    let* _ = typecheck ind in
    type_of t
  | Case (ind, _) ->
    (* Check ind is well-typed *)
    let* _ = typecheck ind in
    type_of t

  | Evar (i, _) -> Context.Monad.to_mut (Context.get_evar_type i)

  | _ -> fun ctx -> raise (TypeError (ctx, IllFormed t))

let rec to_kernel t ctx =
  let open Kernel in
  match t with
  | Var i -> Term.Var i
  | Const (u, s) -> Term.Const (u, s)
  | Fun (tele, t) -> Term.Fun (List.map (fun (s, t) -> (s, to_kernel t ctx)) tele, to_kernel t ctx)
  | App l -> Term.App (List.map (fun t -> to_kernel t ctx) l)
  | Type s -> Term.Type s
  | Pi (tele, t) -> Term.Pi (List.map (fun (s, t) -> (s, to_kernel t ctx)) tele, to_kernel t ctx)
  | Let (s, t, ty, body) -> Term.Let (s, to_kernel t ctx, to_kernel ty ctx, to_kernel body ctx)
  | Ind (a, c) -> Term.Ind (to_kernel a ctx, List.map (fun t -> to_kernel t ctx) c)
  | Construct (ind, i) -> Term.Construct (to_kernel ind ctx, i)
  | Case (ind, r) -> Term.Case (to_kernel ind ctx, r)
  | Evar (i, ictx) ->
    (match Context.get_evar_body i ctx with | None -> raise (TypeError (ctx, NoBody t)) | Some t ->
    let t = subst (fun i -> ictx.(i)) (fun i -> Kernel.Univ.of_atom i 0) t in
    to_kernel t ctx)

let rec of_kernel t =
  let open Kernel in
  match t with
  | Term.Var i -> Var i
  | Term.Const (u, s) -> Const (u, s)
  | Term.Fun (tele, t) -> Fun (List.map (fun (s, t) -> (s, of_kernel t)) tele, of_kernel t)
  | Term.App l -> App (List.map of_kernel l)
  | Term.Type s -> Type s
  | Term.Pi (tele, t) -> Pi (List.map (fun (s, t) -> (s, of_kernel t)) tele, of_kernel t)
  | Term.Let (s, t, ty, body) -> Let (s, of_kernel t, of_kernel ty, of_kernel body)
  | Term.Ind (a, c) -> Ind (of_kernel a, List.map of_kernel c)
  | Term.Construct (ind, i) -> Construct (of_kernel ind, i)
  | Term.Case (ind, r) -> Case (of_kernel ind, r)

let elim_irrelevant_univs body =
  let** body = to_kernel body in
  let body = of_kernel body in
  let** univ = fun ctx -> ctx.univ in
  let* body =
    let renaming = Kernel.Univ.Context.decycle univ in
    let renaming i = Kernel.Univ.of_atom (try IMap.find i renaming with Not_found -> i) 0 in
    let body = subst (fun i -> Var i) renaming body in
    let univ = Kernel.Univ.Context.subst renaming univ in
    fun ctx -> {ctx with univ = univ}, body in
  let* ty = typecheck body in
  let funivs = Utils.ISet.add 0 (free_univs ty) in
  let tunivs = Utils.IMap.fold (fun u _ s -> Utils.ISet.add u s) univ Utils.ISet.empty in
  let bunivs = Utils.ISet.diff tunivs funivs in
  let univ = Utils.ISet.fold Kernel.Univ.Context.elim bunivs univ in
  let _, renaming = IMap.fold (fun v _ (i, renaming) -> i+1, IMap.add v i renaming) univ (0, IMap.empty) in
  let univ = Kernel.Univ.Context.rename (fun i -> IMap.find i renaming) univ in
  let body = subst (fun i -> Var i) (fun i -> Kernel.Univ.of_atom (try IMap.find i renaming with Not_found -> -1) 0) body in
  let ty = subst (fun i -> Var i) (fun i -> Kernel.Univ.of_atom (try IMap.find i renaming with Not_found -> -1) 0) ty in
  fun ctx -> {ctx with univ = univ}, (body, ty)
