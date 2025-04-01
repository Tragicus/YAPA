open Utils

module Atom = struct
  (* Shifted universe *)
  type t = string * int

  let static i = ("", i)

  let compare l l' = Stdlib.compare l l'
end

(* Max of shifted universes *)
type t = int SMap.t

let of_atom v i = SMap.singleton v i

let static i = let v, i = Atom.static i in of_atom v i

let compare u u' = Stdlib.compare u u'

(* For the impredicativity of Prop, the max of levels ("", i) and ("", 0) should be 0 *)
let imax i j = if j = 0 then 0 else max i j

let shift i l = SMap.map (fun j -> j + i) l
let max l l' = SMap.union (fun v i j -> Some ((if v = "" then imax else max) i j)) l l'

type universe_error =
  | LoopAt of string
  | IncompatibleConstraint of t * Atom.t
  | UnsupportedConstraint of t * t

type context = t list SMap.t

exception UnivError of context * universe_error

module Context = struct
  (* Constraint graph, where an arc l -> l' means l <= l'.
     Every constraint of the form
       max(l_1, ..., l_n) <= l' is equivalent to l_1 <= l' /\ ... /\ l_n <= l', so we only
       store constraints of the form l <= l' for l an atomic level.
     Constraints of the form v+i <= l are stored as v <= l-i. *)
  
  type t = context

  let satisfiable g =
    let offset cstr = min 0 (min_smap cstr) in
    let m = max_smap (SMap.map (fun cstrs -> max_list (List.map (fun cstr -> max_smap cstr - offset cstr) cstrs)) g) in
    let f = SMap.map (fun _ -> m) g in
    let rec saturate f updated =
      if SSet.is_empty updated then f else
      let n_updated = SSet.cardinal updated in
      let f, updated = SMap.fold (fun v cstrs (f, updated) ->
          if not (SSet.mem v updated) then (f, updated) else
          let m = max_list (List.map (fun cstr ->
            let offset = offset cstr in
            min_smap (SMap.mapi (fun v i -> SMap.find v f - i) cstr) - 2*offset) cstrs) in
          if SMap.find v f < m then (SMap.add v m f, SSet.add v updated) else (f, updated))
        g (f, SSet.empty) in
      if SSet.cardinal updated = n_updated then raise (UnivError (g, (LoopAt (SSet.choose updated)))) else
      saturate f updated in
    saturate f (SMap.fold (fun v _ -> SSet.add v) g SSet.empty)

  (* Turns an inequality l <= l' into an equivalent constraint graph *)
  let normalize l l' = SMap.map (fun i -> [shift (-i) l']) l

  (* Adds the constraints in g to the constraints in g'. g is expected to be small in comparison to g'. *)
  let add g g' = SMap.union (fun _ c c' -> Some (c @ c')) g g'

  (* Substitute every variable appearing in g with the universe given by subst *)
  let subst subst g =
    let addl l = List.fold_left (fun g g' -> add g' g) SMap.empty l in
    addl (List.map
      (fun (v, cstrs) ->
        let lv = try SMap.find v subst with Not_found -> of_atom v 0 in
        let cstrs = List.map (fun cstr ->
          let cstr = SMap.bindings cstr in
          let cstr = List.map
            (fun (v, i) -> try shift i (SMap.find v subst) with Not_found -> of_atom v i)
            cstr in
          List.fold_left max SMap.empty cstr) cstrs in
        let cstrs = List.map (normalize lv) cstrs in
        addl cstrs)
      (SMap.bindings g))

end
