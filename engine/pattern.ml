(* open Utils *)

type 'a binder = 'a * 'a option
type 'a telescope = 'a binder list
type 'a arity = 'a telescope * 'a

type 'a head =
  | Var of int (* De Bruijn indices *)
  | Const of string
  | Fun of bool (* true if forall *) * 'a telescope * 'a
  | Type
  | Ind of (* arity *) 'a * (* constructors *) 'a list
  | Construct of 'a * int
  | Case of (* inductive *) 'a * (* recursive *) bool
  | Any

module Head = struct
  type 'a t = 'a head

  let map f hd = match hd with
    | Var v -> Var v
    | Const v -> Const v
    | Fun (x, tele, body) -> Fun (x, List.map (fun (ty, t) -> (f ty, Option.map f t)) tele, f body)
    | Type -> Type
    | Ind (a, c) -> Ind (f a, List.map f c)
    | Construct (ind, i) -> Construct (f ind, i)
    | Case (ind, i) -> Case (f ind, i)
    | Any -> Any
end

type pattern = { hd: pattern head; args: pattern list }
type t = pattern

let of_hd hd = { hd; args = [] }

let rec fold fold_hd fold_app t =
  let fold = fold fold_hd fold_app in
  let hd = Head.map fold t.hd in
  let hd = fold_hd hd in
  let args = List.map fold t.args in
  fold_app (hd :: args)

let print t =
  let (+) = String.cat in
  let rec fold_hd = function
    | Var v -> ("_" + string_of_int v, true)
    | Const c -> (c, true)
    | Fun (forall, (ty, Some t) :: tele, body) ->
      let (body, _) = if List.is_empty tele then body else fold_hd (Fun (forall, tele, body)) in
      ("let _ : " + (fst ty) + " := " + (fst t) + " in " + body, false)
    | Fun (forall, tele, body) -> ((if forall then "forall " else "fun ") + String.concat " " (List.map (fun (ty, _) ->
        ("(_ : " + fst ty + ")"
      )) tele) + (if forall then ", " else " => ") + fst body, false)
    | Type -> ("Type", true)
    | Ind (a, c) -> ("ind _ : " + fst a + " :=" + " | " + String.concat " | " (List.map fst c), false)
    | Construct (ind, id) -> ("ind.mk(" + fst ind + ")." + string_of_int id, true)
    | Case (ind, recursive) -> ((if recursive then "ind.fix(" else "ind.case(") + fst ind + ")", true)
    | Any -> ("?", true) in
  let (t, _) = fold fold_hd
    (function
      | [hd] -> hd
      | args -> (String.concat " " (List.map (fun (t, atomic) -> if atomic then t else "(" + t + ")") args), false)) t in
  t

let rec eq pat pat' = 
  let n = List.length pat.args in
  let n' = List.length pat'.args in
  let m, m' = min n n', max n n' in
  let args = List.drop (n - m) pat.args in
  let args' = List.drop (n' - m) pat'.args in
  (match pat.hd, pat'.hd with
  | Any, _ | _, Any -> true
  | _, _ when m <> m' -> false
  | Var i, Var j -> i = j
  | Const v, Const w -> v = w
  | Fun (f, tele, body), Fun (f', tele', body') -> f = f' && List.for_all2 (fun (ty, t) (ty', t') -> eq ty ty' && Option.equal eq t t') tele tele' && eq body body'
  | Type, Type -> true
  | Ind (a, c), Ind (a', c') -> eq a a' && List.for_all2 eq c c'
  | Construct (ind, i), Construct (ind', i') -> i = i' && eq ind ind'
  | Case (ind, r), Case (ind', r') -> r = r' && eq ind ind'
  | _, _ -> false) && List.for_all2 eq args args'


(* TODO: Use discrimination trees. *)
module Map = struct
  type 'a t = (pattern * 'a) list

  let empty : 'a t = []

  let rec find_opt t pat =
    match t with
    | [] -> None
    | (pat', x) :: t -> if eq pat pat' then x else find_opt t pat

  let mem t pat = Option.is_some (find_opt t pat)
  let find t pat = Option.get (find_opt t pat)
  let add pat x t = (pat, x) :: t

  let find_all t pat =
    List.filter_map (fun (pat', x) -> if eq pat pat' then Some x else None) t
end
