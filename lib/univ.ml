open Utils

module Atom = struct
  (* Shifted universe *)
  type t = string * int

  let static i = ("", i)

  let compare l l' = Stdlib.compare l l'
end

(* Max of shifted universes *)
type t = int SMap.t

let of_atom (v, i) = SMap.singleton v i

let static i = of_atom (Atom.static i)

let compare u u' = Stdlib.compare u u'

(* For the impredicativity of Prop, the max of levels ("", i) and ("", 0) should be 0 *)
let imax i j = if j = 0 then 0 else max i j

let shift i l = SMap.map (fun j -> j + i) l
let max l l' = SMap.union (fun v i j -> Some ((if v = "" then imax else max) i j)) l l'

type context = t SMap.t

type universe_error =
  | IncompatibleConstraint of t * Atom.t
  | UnsupportedConstraint of t * t

exception UnivError of context * universe_error

module Context = struct
  (*  Constraint graph, where an arc l -> l' means l <= l'.
      Every constraint of the form
       max(l_1, ..., l_n) <= l' is equivalent to l_1 <= l' /\ ... /\ l_n <= l', so we only
       store constraints of the form l <= l' for l an atomic level.
      Constraints of the form v+i <= l are stored as v <= l-i.
      We do not support l <= max(...)
      *)
  type t = context

  (* Computes the minimum i such that ctx => (v <= v'+i) *)
  let dist ctx v v' =
    let module Heap = Set.Make(struct type t = Atom.t let compare (v, i) (v', i') = if i = i' then String.compare v v' else Int.compare i i' end) in
    let rec aux visited next =
      match Heap.min_elt next with
      | exception _ -> None
      | (w, d) as x ->
        if w = v' then Some d else
        let next = Heap.remove x next in
        if SSet.mem w visited then aux visited next else
        let visited = SSet.add w visited in
        let next = SMap.fold (fun v i -> Heap.add (v, d+i)) (try SMap.find w ctx with _ -> SMap.empty) next in
        aux visited next
    in aux SSet.empty (Heap.singleton (v, 0))

  (* Is (v, i) <= (v', i') a constraint that is compatible with ctx? *)
  let is_compatible_atomic_constraint ctx (v, i) (v', i') =
    match dist ctx v' v with
    | None -> true
    | Some d -> d+i'+1 <= i

  (* Is l <= l' a constraint that is compatible with ctx? *)
  let is_compatible_constraint ctx l l' =
    SMap.for_all (fun v i -> is_compatible_atomic_constraint ctx (v, i) l') l

  let add_constraint ctx l l' =
    if SMap.cardinal l' <> 1 then raise (UnivError (ctx, UnsupportedConstraint (l, l'))) else
    let (v', i') as l' = SMap.choose l' in
    if is_compatible_constraint ctx l l' then
      SMap.fold (fun v i ->
        let i' = i' - i in
        SMap.update v (function | None -> Some (SMap.singleton v' i') | Some m ->
          Some (SMap.update v' (function | None -> Some i' | Some j -> Some (min i' j)) m))) l ctx
    else raise (UnivError (ctx, IncompatibleConstraint (l, l')))
end
