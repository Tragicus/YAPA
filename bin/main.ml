open YAPA

let () =
  try ignore (List.fold_left Commands.eval Term.Context.empty (Parser.toplevel Lexer.token (Lexing.from_channel Stdlib.stdin)))
  with Term.TypeError (ctx, e) -> Term.print_type_error ctx e
