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

let rec eq pat pat' = 
  (match pat.hd, pat'.hd with
  | Any, _ | _, Any -> true
  | Var i, Var j -> i = j
  | Const v, Const w -> v = w
  | Fun (f, tele, body), Fun (f', tele', body') -> f = f' && List.for_all2 (fun (ty, t) (ty', t') -> eq ty ty' && Option.equal eq t t') tele tele' && eq body body'
  | Type, Type -> true
  | Ind (a, c), Ind (a', c') -> eq a a' && List.for_all2 eq c c'
  | Construct (ind, i), Construct (ind', i') -> i = i' && eq ind ind'
  | Case (ind, r), Case (ind', r') -> r = r' && eq ind ind'
  | _, _ -> false) && List.for_all2 eq pat.args pat'.args

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
