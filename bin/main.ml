open YAPA

let () =
  let lexbuf = Lexing.from_channel Stdlib.stdin in
  try ignore (List.fold_left (fun ctx c -> fst (Commands.eval c ctx)) Term.Context.empty (Parser.toplevel Lexer.token lexbuf))
  with | Term.TypeError (ctx, e) ->
    (try Printer.print_type_error ~debug:false e ctx;
    Printer.pp_ctx ctx
    with
    | Term.TypeError _ -> Printer.print_type_error ~debug:true e ctx;
      Printer.pp_ctx ctx)
    | Parser.Error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.printf "Syntax error at line %d, column %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
