open YAPA

let () =
  try ignore (List.fold_left Commands.eval Term.Context.empty (Parser.toplevel Lexer.token (Lexing.from_channel Stdlib.stdin)))
  with Term.TypeError (ctx, e) ->
    (try Term.print_type_error ~debug:true ctx e;
    Term.Context.print ctx
  with
    Term.TypeError _ -> Term.print_type_error ~debug:true ctx e;
    Term.Context.print ctx)
