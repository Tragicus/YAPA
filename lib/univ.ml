open Utils

module Atom = struct
  (* Shifted universe *)
  type t = int * int

  let static i = (0, i)
  let of_var v = (v, 0)

  let compare l l' = Stdlib.compare l l'

  let print (v, i) =
    if v = 0 then print_int i else
      let () = print_string "_"; print_int v in
    if i = 0 then () else
    let () = print_string "+" in
    print_int i
end

(* Max of shifted universes *)
type t = int IMap.t

let of_atom v i = IMap.singleton v i

let static i = let v, i = Atom.static i in of_atom v i

let compare u u' = Stdlib.compare u u'

let isProp u =
  IMap.cardinal u = 1 && IMap.bindings u = [(0, 0)]

(* For the impredicativity of Prop, the max of levels (0, i) and (0, 0) should be 0 *)
let imax i j = if j = 0 then 0 else max i j

let max l l' =
  if isProp l' then l' else
  IMap.union (fun _ i j -> Some (max i j)) l l'

let shift i l = if i = 0 then l else IMap.map (fun j -> j + i) l

let subst subst u =
  IMap.fold (fun v i -> IMap.union (fun _ i j -> Some (Stdlib.max i j)) (shift i (subst v))) IMap.empty u

let rename subst u =
  IMap.fold (fun v i -> IMap.add (subst v) i) IMap.empty u

let print u =
  if IMap.cardinal u = 1 then
    IMap.iter (fun v i -> Atom.print (v, i)) u else
  let () = print_string "max(" in
  Utils.print_with_sep ", " Atom.print (IMap.bindings u)

let free_vars u = IMap.fold (fun u _ s -> ISet.add u s) u ISet.empty

type universe_error =
  | LoopAt of int
  | IncompatibleConstraint of t * Atom.t
  | UnsupportedConstraint of t * t

type context = t list IMap.t

exception UnivError of context * universe_error

(* FIXME: Do I need to remember the number of arguments at which a universe becomes invariant or covariant for cumulativity problems? *)
type covariance =
  | Invariant
  | Covariant of int
  | Contravariant
  | Irrelevant of int

module Context = struct
  (* Constraint graph, where an arc l -> l' means l <= l'.
     Every constraint of the form
       max(l_1, ..., l_n) <= l' is equivalent to l_1 <= l' /\ ... /\ l_n <= l', so we only
       store constraints of the form l <= l' for l an atomic level.
     Constraints of the form v+i <= l are stored as v <= l-i. *)
  
  type t = context

  let empty = IMap.empty

  let satisfiable g =
    let offset cstr = min 0 (min_imap cstr) in
    let m = max_imap (IMap.map (fun cstrs -> max_list (List.map (fun cstr -> max_imap cstr - offset cstr) cstrs)) g) in
    let f = IMap.map (fun _ -> m) g in
    let rec saturate f updated =
      if ISet.is_empty updated then f else
      let n_updated = ISet.cardinal updated in
      let f, updated = IMap.fold (fun v cstrs (f, updated) ->
          if not (ISet.mem v updated) then (f, updated) else
          let m = max_list (List.map (fun cstr ->
            let offset = offset cstr in
            min_imap (IMap.mapi (fun v i -> IMap.find v f - i) cstr) - 2*offset) cstrs) in
          if IMap.find v f < m then (IMap.add v m f, ISet.add v updated) else (f, updated))
        g (f, ISet.empty) in
      if ISet.cardinal updated = n_updated then raise (UnivError (g, (LoopAt (ISet.choose updated)))) else
      saturate f updated in
    saturate f (IMap.fold (fun v _ -> ISet.add v) g ISet.empty)

  (* Turns an inequality l <= l' into an equivalent constraint graph *)
  let normalize l l' = IMap.map (fun i -> [shift (-i) l']) l

  (* Adds the constraints in g' to the constraints in g. g' is expected to be small in comparison to g. *)
  let add g' g = IMap.union (fun _ c' c -> Some (c @ c')) g' g

  let subst_univ = subst
  (* Substitute every variable appearing in g with the universe given by subst *)
  let subst subst g =
    let addl l = List.fold_left add IMap.empty l in
    addl (List.map
      (fun (v, cstrs) ->
        let lv = subst v in
        let cstrs = List.map (fun cstr ->
          let cstr = IMap.bindings cstr in
          let cstr = List.map (fun (v, i) -> shift i (subst v)) cstr in
          List.fold_left max IMap.empty cstr) cstrs in
        let cstrs = List.map (normalize lv) cstrs in
        addl cstrs)
      (IMap.bindings g))

  (* Changes the variable names, assumes there is no capture *)
  let rename subst g =
    IMap.fold (fun v cstrs -> IMap.add (subst v) (List.map (rename subst) cstrs)) IMap.empty g

  (* Creates a new universe *)
  let new_univ g =
    let i = try fst (IMap.max_binding g) + 1 with _ -> 1 in
    let u = of_atom i 0 in
    IMap.add i [] (IMap.update 0 (Option.map (fun l -> u :: l)) g), u

  (* Adds to g the new universes and constraints given by g' *)
  let push_ctx g' g =
    let i = try fst (IMap.max_binding g) + 1 with _ -> 1 in
    let subst j = if j = 0 then j else j + i in
    let g' = rename subst g' in
    match List.tl (IMap.bindings g') with
    | exception _ -> g, []
    | g'u -> add g' g, List.map fst g'u

  let elim u g =
    let ucstrs = IMap.find u g in
    let g = IMap.remove u g in
    IMap.mapi (fun v vcstrs ->
      let ucstrs = List.filter_map (fun cstr ->
        try if 0 < IMap.find v cstr then Some (IMap.remove v cstr) else None
        with _ -> Some cstr) ucstrs in
      List.flatten (List.map (fun vcstr ->
        match IMap.find u vcstr with
        | exception _ -> [vcstr]
        | ui ->
        List.map
          (fun ucstr ->
            let ucstr = shift ui ucstr in
            subst_univ (fun w -> if w = u then ucstr else of_atom w 0) vcstr)
          ucstrs) vcstrs)) g

end
