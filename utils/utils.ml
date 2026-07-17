module List = struct
  include List

  let uncons = function
    | [] -> failwith "uncons"
    | x :: q -> (x, q)

  (* `split_last_at acc i [x_0; ...; x_n]` = `([x_0; ...; x_(i-1)] @ List.rev acc, [x_i; ...; x_n]` *)
  let rec split_at ?(acc=[]) i l =
    if i = 0 then List.rev acc, l else
    match l with
    | [] -> raise Not_found
    | x :: l -> split_at ~acc:(x :: acc) (i-1) l

  let to_json value_to_json l = `List (List.map value_to_json l)
  let of_json value_of_json j = List.map value_of_json (Yojson.Basic.Util.to_list j)
end

module Map = struct
  module Make(T: sig include Map.OrderedType val print : t -> string end) = struct
    include Stdlib.Map.Make(T)

    let print pp_elt m =
      let (+) = String.cat in
      "{ " + String.concat ", " (List.map (fun (i, v) -> T.print i + " -> " + pp_elt v) (to_list m)) + " }"

    let to_json key_to_json value_to_json m = List.to_json (fun (k, v) -> `Assoc [ ("key", key_to_json k); ("value", value_to_json v) ]) (to_list m)
    let of_json key_of_json value_of_json j = of_list (List.of_json (fun j ->
      (key_of_json (Yojson.Basic.Util.member "key" j), value_of_json (Yojson.Basic.Util.member "value" j))) j)
  end
end

module Set = struct
  module Make(T: sig include Set.OrderedType val print : t -> string end) = struct
    include Stdlib.Set.Make(T)

    let print m =
      let (+) = String.cat in
      "{ " + String.concat ", " (List.map T.print (to_list m)) + " }"

    let to_json value_to_json m = List.to_json value_to_json (to_list m)
    let of_json value_of_json j = of_list (List.of_json value_of_json j)
  end
end
module String = struct
  include String
  let print s = s
  let to_json s = `String s
  let of_json = Yojson.Basic.Util.to_string
end
module Int = struct
  include Int
  let (+) = (+)
  let print = string_of_int
  let to_json i = `Int i
  let of_json = Yojson.Basic.Util.to_int
end
module SMap = Map.Make(String)
module SSet = Set.Make(String)
module IMap = Map.Make(Int)
module ISet = Set.Make(Int)

module Option = struct
  include Option

  let swap = function
    | None -> Some None
    | Some None -> None
    | Some (Some x) -> Some (Some x)

  let map_or x f = function
    | None -> x
    | Some x -> f x

  let to_json value_to_json x = List.to_json value_to_json (Option.to_list x)
  let of_json value_of_json j = List.nth_opt (List.of_json value_of_json j) 0
end

module Random = struct
  include Random

  let int () = 100000000 + Random.int 899999999
end

let timestamp x =
  let s = string_of_int (Random.int x) in
  s ^ String.make (9 - String.length s) ' '

let min_smap m = SMap.fold (fun _ -> min) m max_int
let max_smap m = SMap.fold (fun _ -> max) m min_int
let min_imap m = IMap.fold (fun _ -> min) m max_int
let max_imap m = IMap.fold (fun _ -> max) m min_int
let min_list l = List.fold_left min max_int l
let max_list l = List.fold_left max min_int l

let print_with_sep sep printer = function
  | [] -> ()
  | pp :: pps ->
    let () = printer pp in
    List.iter (fun pp -> print_string sep; printer pp) pps

module ContextMonad(T : sig type t end) = struct
  (* mutable state: function that computes an object of type 'a, potentially modifying the context. *)
  type 'a t = T.t -> T.t * 'a
  (* immutable state: function that computes an object of type 'a without modifying the context. *)
  type 'a it = T.t -> 'a

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

    let rec exists f = function
      | [] -> ret false
      | x :: l ->
        let* b = f x in
        if b then ret b else exists f l

    let rec fold_left f l acc = match l with
      | [] -> ret acc
      | x :: l ->
        let* acc = f x acc in
        fold_left f l acc
      
  end

  module Option = struct
    let map (f : 'a -> 'b t) = function
      | None -> ret None
      | Some x -> let+ x = f x in Some x

    let bind x f =
      let* x = x in
      match x with
      | None -> ret None
      | Some x -> f x
  end
end

(* max heap of integers *)
(*module MaxHeap = struct
  type t = int Dynarray.t

  let create = Dynarray.create

  let add x t =
    let i = ref Dynarray.length t in
    Dynarray.add_last t x;
    while !i <> 0 && (Dynarray.get t ((!i - 1) / 2) < x || Dynarray.get t (!i / 2 - 1) < x) do
      let y = Dynarray.get t (!i / 2 - 1) in
      if y < x then
        Dynarray.set t !i y;
        i := !i / 2 - 1;
        Dynarray.set t !i x else
      let y = Dynarray.get t ((!i - 1) / 2) in
      Dynarray.set t !i y;
      i := (!i - 1) / 2;
      Dynarray.set t !i x
    done

  let top t = if Dynarray.is_empty t then raise Not_found else Dynarray.get t 0

  let pop t =
    if Dynarray.is_empty t then raise Not_found else
    let r = Dynarray.get t 0 in
    let x = Dynarray.pop_last t in
    Dynarray.set t 0 x;
    while (2 * !i + 1 < Dynarray.length t && x < Dynarray.get t (2 * !i + 1)) || (2 * (!i + 1) < Dynarray.length t && x < Dynarray.get t (2 * (!i + 1))) do
      let y = Dynarray.get t (2 * !i + 1) in
      if x < y then 
        Dynarray.set t !i y;
        i := 2 * !i + 1;
        Dynarray.set t !i x else
      let y = Dynarray.get t (2 * (!i + 1)) in
      Dynarray.set t !i y;
      i := 2 * (!i + 1);
      Dynarray.set t !i x
    done;
    r
end*)

let fresh_name base vars =
  if not (List.mem base vars) then base else
  let ids = List.filter_map (fun var ->
    if not (String.starts_with ~prefix:base var) then None else
    let start = String.length base in
    let id = String.sub var start (String.length var - start) in
    if String.length id = 0 then None else
    if String.get id 0 = '0' && String.length id <> 1 then None else
    try Some (int_of_string id) with _ -> None
  ) vars in
  let rec purge_max ids n =
    try if ISet.max_elt ids = n then purge_max (ISet.remove n ids) (n - 1) else ids, n
    with _ -> ids, n in
  let _, n = List.fold_left (fun (ids, n) id ->
    if n <= id || ISet.mem id ids then purge_max ids (n - 1) else
    ISet.add id ids, n
  ) (ISet.empty, List.length ids) ids in
  base ^ string_of_int n


