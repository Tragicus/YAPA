module SMap = Map.Make(String)
module SSet = Set.Make(String)

(* `split_last_at acc i [x_1; ...; x_n]` = `([x_1; ...; x_(i-1)] @ List.rev acc, [x_i; ...; x_n]` *)
let rec split_list_at ?(acc=[]) i l =
  if i = 0 then List.rev acc, l else
  match l with
  | [] -> raise Not_found
  | x :: l -> split_list_at ~acc:(x :: acc) (i-1) l
