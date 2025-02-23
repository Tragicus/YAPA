
type t =
  | Print of Term.t
  | Check of Term.t
  | Define of string * Term.t * Term.t

let eval ctx = function
  | Print (Const c) ->
    let () = Term.print ctx (Term.Context.get_const_body ctx c) in
    let () = print_newline () in
    ctx
  | Print _ ->
    failwith "I can only print the body of constants"
  | Check t ->
    let () = Term.print ctx (Term.type_of ctx t) in
    let () = print_newline () in
    ctx
  | Define (v, ty, body) ->
    if Term.unify ctx (Term.type_of ctx body) ty 
      then Term.Context.push_const ctx v (ty, body)
    else raise (Term.TypeError (ctx, Term.TypeMismatch (ty, body)))

