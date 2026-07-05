open Utils

module Sort = struct
  type t = | SProp | Prop | Type | Var of int

  let is_var = function | Var(_) -> true | _ -> false

  let compare s s' = Stdlib.compare s s'

  let print = function
    | SProp -> "SProp"
    | Prop -> "Prop"
    | Type -> "Type"
    | Var s -> String.cat "s_" (string_of_int s)

  let subst ss s = match s with | Var s -> IMap.find s ss | _ -> s

  let free_vars s = match s with | Var s -> ISet.singleton s | _ -> ISet.empty
end

module Level = struct
  (* Max of shifted universes *)
  type t = int IMap.t

  let of_var u = IMap.of_list [(u, 0)]
  let base = of_var 0

  let add i l = IMap.map (fun j -> j + i) l

  let succ = add 1

  let max = IMap.merge (fun _ x y -> match x, y with
    | None, x | x, None -> x
    | Some i, Some j -> Some (max i j))

  (* Weak comparison, where u <= v iff u <= v pointwise.
   * This may return Less or Greater even when assignations do not enforce said inequality. *)
  let wcmp l l' =
    let update cmp cmp' = if cmp = None || cmp = Some cmp' then Some cmp' else None in
    let rec aux cmp l l' = match l, l' with
      | [], [] -> update cmp 0
      | [], _ -> update cmp (-1)
      | _, [] -> update cmp 1
      | (u, n) :: l, (v, m) :: l' ->
        if u < v then aux (update cmp 1) l ((v, m) :: l') else
        if v < u then aux (update cmp (-1)) ((u, n) :: l) l' else
        aux (update cmp (if n < m then -1 else if m < n then 1 else 0)) l l' in
    aux None (IMap.to_list l) (IMap.to_list l')

  let wle l l' = let cmp = wcmp l l' in cmp = Some (-1) || cmp = Some 0

  let print l =
    let (+) = String.cat in
    let print_atom (v, n) = 
      if v = 0 then string_of_int n else
      "u_" + string_of_int v + (if n = 0 then "" else " + " + string_of_int n) in
    match List.map print_atom (IMap.to_list l) with
    | [] -> failwith "Anomaly: empty universe level"
    | [s] -> s
    | s :: l -> "max(" + String.concat ", " (s :: l) + ")"

  let subst su u =
    IMap.fold (fun u n v -> max v (add n (IMap.find u su))) u IMap.empty

  let free_vars u = IMap.fold (fun u _ -> ISet.add u) u ISet.empty
end

type t = Sort.t * Level.t

let add i ((s, l): t) = (s, Level.add i l)

let succ = add 1

(* Universe of a product type. *)
(* Approximation, when `s'` is `SProp` or `Prop`, `l` should not matter, but the theory is not well-behaved with this rule. *)
let max (_, l) (s, l') = (s, Level.max l l')

let sprop = (Sort.SProp, Level.base)
let prop = (Sort.Prop, Level.base)
let set = (Sort.Type, Level.base)

let print (s, l) =
  let (+) = String.cat in
  Sort.print s + "@{" + Level.print l + "}"

type context = {
  sorts: (string option * Sort.t * Sort.t * ISet.t * ISet.t) IMap.t;
  levels: (string option (* name *) * int (* model *) * Level.t list (* upper bounds *)) IMap.t;
}

type univ_error =
  | UnboundSort of int
  | UnboundLevel of int
  | SortInconsistency of Sort.t * Sort.t
  | UnivInconsistency of Level.t * Level.t

exception UnivError of context * univ_error

let print_error = function
  | UnboundSort i -> "Unbound sort " ^ string_of_int i
  | UnboundLevel i -> "Unbound universe level " ^ string_of_int i
  | SortInconsistency (s, t) -> "Inconsistent sort constraint : " ^ Sort.print s ^ " <= " ^ Sort.print t
  | UnivInconsistency (u, v) -> "Inconsistent universe constraint : " ^ Level.print u ^ " <= " ^ Level.print v

module Context = struct
  type t = context

  let empty = {
    sorts = IMap.empty;
    levels = IMap.of_list [(0, (Some "", 0, []))]
  }

  let print ctx =
    let (+) = String.cat in
    String.concat "\n" ("sorts:" ::
      List.map (fun (i, (_, lb, ub, lbs, ubs)) -> 
        "\t { " + (String.concat ", " (List.map Sort.print (lb :: (List.map (fun i -> Sort.Var i) (ISet.to_list lbs))))) + " } <= " + (Sort.print (Sort.Var i)) + " <= { " +
          (String.concat ", " (List.map Sort.print (ub :: (List.map (fun i -> Sort.Var i) (ISet.to_list ubs))))) + " }") (IMap.to_list ctx.sorts) @
      "levels:" ::
      List.map (fun (i, (_, m, ubs)) ->
        "\t " + Level.print (Level.of_var i) + "@{" + string_of_int m + "} <= { " + (String.concat ", " (List.map Level.print ubs)) + " }"
      ) (IMap.to_list ctx.levels))


  module Monad = Utils.ContextMonad(struct type u = t type t = u end)
  open Monad.Notations

  let new_sort name ctx =
    let s = try fst (IMap.max_binding ctx.sorts) + 1 with _ -> 0 in
    { ctx with sorts = IMap.add s (name, Sort.SProp, Sort.Type, ISet.empty, ISet.empty) ctx.sorts }, Sort.Var s

  let new_level name ctx =
    let u = fst (IMap.max_binding ctx.levels) + 1 in
    { sorts = ctx.sorts;
      levels = IMap.add u (name, 0, []) (IMap.update 0 (Option.map (fun (s, i, l) -> (s, i, Level.of_var u :: l))) ctx.levels)
    }, Level.of_var u

  let new_univ s u =
    let* s = new_sort s in
    let+ u = new_level u in
    (s, u)

  (* Adding a constraint [s1 <= s2] to the context of sorts. *)
  let add_sort_constraint s1 s2 ctx =
    let get s ctx = try IMap.find s ctx.sorts with _ -> raise (UnivError (ctx, UnboundSort s)) in
    (* Propagates the constraint l <= s in the graph of sort variables constraints *)
    let rec propagate_up seen l s ctx =
      if ISet.mem s seen then ctx, seen else
      let (n, ls, us, lb, ub) = get s ctx in
      if l <= ls then ctx, seen else
      ISet.fold (fun s (ctx, seen) -> propagate_up seen l s ctx) ub ({ ctx with sorts = IMap.add s (n, l, us, lb, ub) ctx.sorts }, ISet.add s seen) in
    (* Propagates the constraint s <= u in the graph of sort variables constraints *)
    let rec propagate_down seen u s ctx =
      if ISet.mem s seen then ctx, seen else
      let (n, ls, us, lb, ub) = get s ctx in
      if us <= u then ctx, seen else
      ISet.fold (fun s (ctx, seen) -> propagate_down seen u s ctx) lb ({ ctx with sorts = IMap.add s (n, ls, u, lb, ub) ctx.sorts }, ISet.add s seen) in
    try match s1, s2 with
    | Sort.Var s1, Sort.Var s2 -> 
      let (_, l1, _, _, _) = get s1 ctx in
      let (_, _, u2, _, _) = get s2 ctx in
      if u2 < l1 then raise (UnivError (ctx, SortInconsistency (u2, l1))) else
      let ctx = { ctx with sorts = IMap.update s1 (Option.map (fun (n, l, s, lb, ub) -> (n, l, s, lb, ISet.add s2 ub))) ctx.sorts } in
      let ctx = { ctx with sorts = IMap.update s2 (Option.map (fun (n, l, s, lb, ub) -> (n, l, s, ISet.add s1 lb, ub))) ctx.sorts } in
      let ctx, _ = propagate_up ISet.empty l1 s2 ctx in
      fst (propagate_down ISet.empty u2 s1 ctx), ()
    | Sort.Var s1, s2 ->
      let (_, l1, u1, _, _) = get s1 ctx in
      if s2 < l1 then raise (UnivError (ctx, SortInconsistency (s2, l1))) else
      let ctx, _ = propagate_down ISet.empty u1 s1 ctx in
      ctx, ()
    | s1, Sort.Var s2 ->
      let (_, l2, u2, _, _) = get s2 ctx in
      if u2 < s1 then raise (UnivError (ctx, SortInconsistency (u2, s1))) else
      let ctx, _ = propagate_up ISet.empty l2 s2 ctx in
      ctx, ()
    | s1, s2 ->
      if s2 < s1 then raise (UnivError (ctx, SortInconsistency (s2, s1))) else
      ctx, ()
    with e ->
      let () = print_endline ("inconsistent sort constraint " ^ Sort.print s1 ^ " <= " ^ Sort.print s2 ^ " in\n" ^ print ctx) in
      raise e

  exception Loop of ISet.t

  let saturate_model =
    let** _ = let+* (_, _, ubs) = fun ctx -> IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    let get_level u = fun ctx -> try IMap.find u ctx.levels with _ -> raise (UnivError (ctx, UnboundLevel u)) in
    let ret = Monad.ret in
    let rec saturate_over dom =
      let* updt = Monad.List.fold_left (fun u updt ->
        let** (_, m, ubs) = get_level u in
        Monad.List.fold_left (fun v updt ->
          let* v = Monad.List.map (fun (v, m) -> let** (_, k, _) = get_level v in ret (k - m)) (IMap.to_list v) in
          let k = match v with
            | [] -> failwith "Anomaly: empty universe level"
            | i :: l -> List.fold_left min i l in
          if m < k then
            let+ () = fun ctx -> { ctx with levels = IMap.update u (Option.map (fun (v, _, ubs) -> (v, k, ubs))) ctx.levels }, () in
            ISet.add u updt
          else ret updt
        ) ubs updt
      ) (ISet.to_list dom) ISet.empty in
      if ISet.is_empty updt then ret () else
      if ISet.cardinal updt = ISet.cardinal dom then raise (Loop updt) else
      saturate_onto updt
    and saturate_onto dom =
      let* () = saturate_over dom in
      let* progress = Monad.List.fold_left (fun u progress ->
        let** (_, m, ubs) = get_level u in
        let ubs = List.filter (fun v -> IMap.for_all (fun v _ -> ISet.mem v dom) v) ubs in
        Monad.List.fold_left (fun v progress ->
          let* v = Monad.List.map (fun (v, m) -> let** (_, k, _) = get_level v in ret (k - m)) (IMap.to_list v) in
          let k = match v with
            | [] -> failwith "Anomaly: empty universe level"
            | i :: l -> List.fold_left min i l in
          if m < k then
            let+ () = fun ctx -> { ctx with levels = IMap.update u (Option.map (fun (v, _, ubs) -> (v, k, ubs))) ctx.levels }, () in
            true
          else ret progress
        ) ubs progress 
      ) (ISet.to_list dom) false in
      if progress then saturate_onto dom else ret () in
    fun ctx -> saturate_over (ISet.of_list (List.map fst (IMap.to_list ctx.levels))) ctx

  (* Adding a constraint [u1 <= u2] to the context of universe levels. *)
  let add_level_constraint u1 u2 ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    let ctx = List.fold_left (fun ctx (u, n) ->
      if try let m = IMap.find u u2 in n <= m with _ -> false then ctx else
      let u2 = IMap.remove u u2 in
      if IMap.is_empty u2 then ctx else
      let u2 = Level.add (- n) u2 in
      let (name, m, ubs) = try IMap.find u ctx.levels with _ -> raise (UnivError (ctx, UnboundLevel u)) in
      let ditch = ref false in
      let ubs = List.filter (fun v -> !ditch ||
        match Level.wcmp v u2 with
        | None -> true
        | Some 1 -> false
        | _ -> (ditch := true; true)
      ) ubs in
      let ubs = if !ditch then ubs else u2 :: ubs in
      { ctx with levels = IMap.add u (name, m, ubs) ctx.levels }
    ) ctx (IMap.to_list u1) in
    try let r = saturate_model ctx in
      let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
      r
    with Loop _ ->
      let () = print_endline ("inconsistent level constraint " ^ Level.print u1 ^ " <= " ^ Level.print u2 ^ " in\n" ^ print ctx) in
      raise (UnivError (ctx, UnivInconsistency (u1, u2)))

  let add_constraint u1 u2 =
    let (s1, u1) = u1 in
    let (s2, u2) = u2 in
    let* () = add_sort_constraint s1 s2 in
    let* () = add_sort_constraint s2 s1 in
    add_level_constraint u1 u2

  (* Removes `s` from the graph of sort levels. *)
  let instantiate_sort s ctx =
    let (_, _, _, lbs, ubs) = try IMap.find s ctx.sorts with _ -> raise (UnivError (ctx, UnboundSort s)) in
    let lbs = ISet.remove s lbs in
    let ubs = ISet.remove s ubs in

    { ctx with sorts = IMap.map (fun (n, l, u, lb, ub) ->
      (n, l, u,
        (if ISet.mem s lb then ISet.union lbs (ISet.remove s lb) else lb),
        if ISet.mem s ub then ISet.union ubs (ISet.remove s ub) else ub)
      ) ctx.sorts
    }, ()

  (* Replaces `l` by `u` in the graph of universe level variables (except from the upper bounds of `0`).
   * Assumes that this instantiation is correct, i.e. does not change the set of valid
   * instantiations for the other level variables. *)
  let instantiate_level l u ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    { ctx with levels = IMap.mapi (fun v (name, m, ubs) -> (name, m,
        if v == l then [] else
        List.filter_map (fun ub ->
          match IMap.find_opt l ub with
          | None -> Some ub
          | Some n ->
          if Option.value ~default:true (Option.map (fun m -> 0 <= m + n) (IMap.find_opt v u)) then None else
          let u = IMap.remove l u in
          Some (Level.max ub (Level.add n u))
        ) ubs)
      ) ctx.levels
    }, ()

  (* Removes a level variable from the context, returning a minimal level that may be equal to
   * that level variable according to the current constraints. *)
  let minimize_level u ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    if u = 0 then failwith "Anomaly: cannot minimize bottom universe" else
    let lb = IMap.fold (fun v (_, _, ubs) lb ->
      if v = u then lb else
      let rec loop l lb = function
        | [] -> lb
        | ub :: r ->
            if not (IMap.mem u ub) then loop (ub :: l) lb r else
            let n = IMap.find u ub in
            if IMap.cardinal ub = 1 then loop l (Level.max lb (IMap.singleton v (- n))) r else
            let ub = IMap.remove u ub in
            try let _ = add_level_constraint (IMap.singleton u n) ub ctx in
              loop (IMap.singleton u n :: l) (Level.max lb (IMap.singleton v (- n))) r 
            with UnivError (_, UnivInconsistency (_, _)) ->
            loop (ub :: l) (Level.max lb (Level.add (1 - n) ub)) r in
      loop [] lb ubs
    ) ctx.levels IMap.empty in
    fst (instantiate_level u lb ctx), lb

  let minimize_model ctx = saturate_model { ctx with levels = IMap.map (fun (v, _, ubs) -> (v, 0, ubs)) ctx.levels }

  let append ctx' ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx'.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    let ns = Option.map_or 0 (fun (ns, _) -> ns + 1) (IMap.max_binding_opt ctx.sorts) in
    let nu = fst (IMap.max_binding ctx.levels) in
    let newsorts = List.init (IMap.cardinal ctx'.sorts) (fun i -> Sort.Var (ns + i)) in
    let newunivs = List.init (fst (IMap.max_binding ctx'.levels)) (fun i -> Level.of_var (nu + i + 1)) in
    let ss = IMap.mapi (fun n _ -> n + ns) ctx'.sorts in
    let sorts = IMap.fold (fun n (name, l, u, lbs, ubs) ->
      IMap.add (n + ns) (name, l, u, ISet.map (fun n -> n + ns) lbs, ISet.map (fun n -> n + ns) ubs)) ctx'.sorts ctx.sorts in
    let su = IMap.mapi (fun n _ -> if n = 0 then 0 else n + nu) ctx'.levels in

    let (_, nm, _) = IMap.find 0 ctx.levels in
    let (_, nm', _) = IMap.find 0 ctx'.levels in
    let nmm = Int.max nm nm' in
    let levels = IMap.map (fun (v, m, ubs) -> (v, m + nmm - nm, ubs)) ctx.levels in
    let levels' = IMap.of_list (List.map (fun (n, (name, m, ubs)) ->
      let ubs = List.map (fun ub -> IMap.of_list (List.map (fun (v, n) -> ((if v = 0 then v else v + nu), n)) (IMap.to_list ub))) ubs in
      ((if n = 0 then n else n + nu), (name, m + nmm - nm', ubs))
    ) (IMap.to_list ctx'.levels)) in
    let levels = IMap.union (fun _ (nl, m, l) (_, _, r) -> Some (nl, m, l @ r)) levels levels' in

    { sorts; levels }, ((newsorts, newunivs), (ss, su))

  (* Prunes the sort and level variables that do not appear in fs and fu respectively, returning
   * the substitutions to apply to terms from the input context. *)
  let keep_univs fs fu ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> (not (IMap.mem 0 u)) || (not (IMap.cardinal u = 1)) || 0 <= IMap.find 0 u) ubs) in
    (* Ensuring that we keep 0. *)
    let fu = ISet.add 0 fu in
    (* We instantiate every sort variable outside of fs by its upper bound.
     * We also rename the sort variables we keep so that they form an initial segment of NN. *)
    let ctx, ss, _ = IMap.fold (fun s (_, _, u, _, _) (ctx, ss, k) ->
      if ISet.mem s fs then (ctx, IMap.add s (Sort.Var k) ss, k + 1) else
      (fst (instantiate_sort s ctx), IMap.add s u ss, k)
    ) ctx.sorts (ctx, IMap.empty, 0) in
    (* We minimize every level variable outside of fu.
     * We also rename the level variables we keep so that they form an initial segment of NN. *)
    let ctx, su, _ = IMap.fold (fun u _ (ctx, su, k) ->
      if ISet.mem u fu then (ctx, IMap.add u (Level.of_var k) su, k + 1) else
      let ctx, v = minimize_level u ctx in
      (ctx, IMap.add u v su, k)
    ) ctx.levels (ctx, IMap.empty, 0) in
    (* For any u < self.levels.len(), if fu contains u then substu[u] contains the new name
     * of u. Otherwise, either substs[u] is an explicit level in terms of kept level variables
     * and larger variables.

     * We compute the substitutions of the old level variables in terms of the new level
     * variables. *)
    let su = List.fold_right (fun u su ->
      if ISet.mem u fu then su else
      IMap.add u (Level.subst su (IMap.find u su)) su
    ) (List.map fst (IMap.to_list ctx.levels)) su in
    (* We perform the renaming in the context. *)
    let sorts =
      let dest_var = function | Sort.Var s -> s | _ -> failwith "unreachable" in
      let rename s = dest_var (IMap.find s ss) in
      IMap.of_list (List.map (fun (s, (n, l, u, lbs, ubs)) -> (rename s, (n, l, u, ISet.map rename lbs, ISet.map rename ubs))) (List.filter (fun (s, _) -> ISet.mem s fs) (IMap.to_list ctx.sorts))) in
    let rename u = fst (IMap.min_binding (IMap.find u su)) in
    let levels = IMap.of_list (List.map (fun (u, (n, m, ubs)) -> (rename u, (n, m, List.map (fun u -> IMap.of_list (List.map (fun (u, n) -> (rename u, n)) (IMap.to_list u))) ubs))) (List.filter (fun (u, _) -> ISet.mem u fu) (IMap.to_list ctx.levels))) in
    { sorts; levels }, (ss, su)

  let sort_upper_bounds s ctx =
    let rec aux s visited =
      if ISet.mem s visited then visited else
      let visited = ISet.add s visited in
      let (_, _, _, _, ubs) = try IMap.find s ctx.sorts with _ -> raise (UnivError (ctx, (UnboundSort s))) in
      ISet.fold aux ubs visited in
    aux s ISet.empty

  let sort_lower_bounds s ctx =
    let rec aux s visited =
      if ISet.mem s visited then visited else
      let visited = ISet.add s visited in
      let (_, _, _, lbs, _) = try IMap.find s ctx.sorts with _ -> raise (UnivError (ctx, (UnboundSort s))) in
      ISet.fold aux lbs visited in
    aux s ISet.empty

  (* Prunes the sort and level variables that are provably equal to some other sort and levels, returning
   * the substitutions to apply to term from the input context. *)
  let optimize ctx =
    let _ = let (_, _, ubs) = IMap.find 0 ctx.levels in assert (List.for_all (fun u -> not (IMap.mem 0 u) || not (IMap.cardinal u = 1) || 0 <= IMap.find 0 u) ubs) in
    (* We instatiate every sort variable which is provably equal to an explicit sort. *)
    let ctx, fs, ss = IMap.fold (fun s (_, l, u, _, _) (ctx, fs, ss) ->
      if l = u then (fst (instantiate_sort s ctx), fs, IMap.add s u ss) else (ctx, ISet.add s fs, IMap.add s (Sort.Var s) ss)
    ) ctx.sorts (ctx, ISet.empty, IMap.empty) in
    (* We instatiate every sort variable which is provably equal to a larger one. *)
    let fs, ss, _ = IMap.fold (fun s _ (fs, ss, k) ->
      if not (ISet.mem s fs) then (fs, ss, k) else
      let ubs = ISet.filter (fun s' -> s < s' && (ISet.mem s' fs)) (sort_upper_bounds s ctx) in
      let lbs = ISet.filter (fun s' -> s < s' && (ISet.mem s' fs)) (sort_lower_bounds s ctx) in

      (* We take the maximum element (if it exists), which is guaranteed to not be itself instantiated. *)
      match ISet.max_elt_opt (ISet.inter ubs lbs) with
      | Some s' -> (ISet.remove s fs, IMap.add s (Sort.Var s') ss, k)
      | None -> (fs, IMap.add s (Sort.Var k) ss, k + 1)
    ) ctx.sorts (fs, ss, 0) in

    let ss = IMap.mapi (fun s s' -> if ISet.mem s fs then s' else match s' with | Sort.Var s' -> IMap.find s' ss | _ -> s') ss in

    let ctx, fu, su, _ = IMap.fold (fun u _ (ctx, fu, su, k) ->
      if u = 0 then (ctx, ISet.add 0 fu, IMap.add 0 (Level.of_var 0) su, k + 1) else
      let lb = IMap.fold (fun v (_, _, ubs) lb ->
        match List.filter_map (fun ub ->
          if IMap.cardinal ub <> 1 then None else
          let (v, n) = IMap.min_binding ub in
          if v = u then Some (-n) else None
        ) ubs with
        | [] -> lb
        | n :: l -> let n = List.fold_left Int.max n l in IMap.add v n lb
      ) ctx.levels IMap.empty in
      let _ = assert (not (IMap.is_empty lb)) in
      if List.exists (fun ub -> Level.wle ub lb) (try let (_, _, ubs) = IMap.find u ctx.levels in ubs with _ -> raise (UnivError (ctx, UnboundLevel u))) then
        (fst (instantiate_level u lb ctx), fu, IMap.add u lb su, k) else
      (ctx, ISet.add u fu, IMap.add u (Level.of_var k) su, k + 1)
    ) ctx.levels (ctx, ISet.empty, IMap.empty, 0) in
    (* For any u, if fu contains u then su[u] contains the new name
     * of u. Otherwise, either su[u] is an explicit level in terms of kept level variables
     * and larger variables.

     * We compute the substitutions of the old level variables in terms of the new level
     * variables. *)
    let su = List.fold_right (fun u su ->
      if ISet.mem u fu then su else
      IMap.add u (Level.subst su (IMap.find u su)) su
    ) (List.map fst (IMap.to_list ctx.levels)) su in
    (* We perform the renaming in the context. *)
    let sorts =
      let dest_var = function | Sort.Var s -> s | _ -> failwith "unreachable" in
      let rename s = dest_var (IMap.find s ss) in
      IMap.of_list (List.map (fun (s, (n, l, u, lbs, ubs)) -> (rename s, (n, l, u, ISet.map rename lbs, ISet.map rename ubs))) (List.filter (fun (s, _) -> ISet.mem s fs) (IMap.to_list ctx.sorts))) in
    let rename u = fst (IMap.min_binding (IMap.find u su)) in
    let levels = IMap.of_list (List.map (fun (u, (n, m, ubs)) -> (rename u, (n, m, List.map (fun u -> IMap.of_list (List.map (fun (u, n) -> (rename u, n)) (IMap.to_list u))) ubs))) (List.filter (fun (u, _) -> ISet.mem u fu) (IMap.to_list ctx.levels))) in
    { sorts; levels }, (ss, su)

end
