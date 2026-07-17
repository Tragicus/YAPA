open Utils

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

let binder_to_json value_to_json (ty, t) = `List [ value_to_json ty; Option.to_json value_to_json t ]

let head_to_json value_to_json = function
  | Var i -> `Assoc [ ("var", (Int.to_json i : Yojson.Basic.t)) ]
  | Const s -> `Assoc [ ("const", String.to_json s) ]
  | Fun (f, tele, body) -> `Assoc [ ((if f then "forall" else "fun"), `List [ List.to_json (binder_to_json value_to_json) tele; value_to_json body ]) ]
  | Type -> `Assoc [ ("type", Int.to_json 0) ]
  | Ind (a, c) -> `Assoc [ ("ind", `List [ value_to_json a; List.to_json value_to_json c ]) ]
  | Construct (ind, i) -> `Assoc [ ("mk", `List [ value_to_json ind; Int.to_json i ]) ]
  | Case (ind, r) -> `Assoc [ ("match", `List [ value_to_json ind; Int.to_json (if r then 1 else 0) ]) ]
  | Any -> `Assoc [ ("any", Int.to_json 0) ]

let binder_of_json value_of_json j = 
  match List.of_json (fun x -> x) j with
  | ty :: t :: [] -> (value_of_json ty, Option.of_json value_of_json t)
  | _ -> raise (Invalid_argument "head_of_json.tele")

let head_of_json value_of_json j =
  match List.hd (Yojson.Basic.Util.keys j) with
  | "var" -> Var (Int.of_json (Yojson.Basic.Util.member "var" j))
  | "const" -> Const (String.of_json (Yojson.Basic.Util.member "const" j))
  | ("forall" | "fun" ) as k ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member k j) with
    | tele :: body :: [] -> Fun (k = "forall", List.of_json (binder_of_json value_of_json) tele, value_of_json body)
    | _ -> raise (Invalid_argument ("head_of_json." ^ k)))
  | "type" -> Type
  | "ind" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "ind" j) with
    | a :: c :: [] -> Ind (value_of_json a, List.of_json value_of_json c)
    | _ -> raise (Invalid_argument "head_of_json.ind"))
  | "mk" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "mk" j) with
    | ind :: i :: [] -> Construct (value_of_json ind, Int.of_json i)
    | _ -> raise (Invalid_argument "head_of_json.mk"))
  | "match" ->
    (match List.of_json (fun x -> x) (Yojson.Basic.Util.member "match" j) with
    | ind :: r :: [] -> Case (value_of_json ind, Int.of_json r = 1)
    | _ -> raise (Invalid_argument "head_of_json.match"))
  | "any" -> Any
  | _ -> raise (Invalid_argument "head_of_json")

let rec to_json t =
  `Assoc [ ("hd", head_to_json to_json t.hd); ("args", List.to_json to_json t.args) ]

let rec of_json j =
  { hd = head_of_json of_json (Yojson.Basic.Util.member "hd" j); args = List.of_json of_json (Yojson.Basic.Util.member "args" j) }

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

  let to_json value_to_json = List.to_json (fun (pat, x) -> `Assoc [ ("pattern", to_json pat); ("value", value_to_json x) ])
  let of_json value_of_json = List.of_json (fun j -> (of_json (Yojson.Basic.Util.member "pattern" j), value_of_json (Yojson.Basic.Util.member "value" j)))
end
