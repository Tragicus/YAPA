open Yapa

let () =
  let () = Random.init 0 in
  let file = ref "" in
  let () = Arg.parse [] (fun s -> file := s) "" in
  let lexbuf = Lexing.from_channel (if !file = "" then Stdlib.stdin else open_in !file) in
  let () = Tactic.parse_hint := fun hint ->
    Parser.toptactic Lexer.token (Lexing.from_string (hint ^ ".")) in
  match (Term.Context.Monad.List.fold_left (fun c () -> Commands.eval c) (Parser.toplevel Lexer.token lexbuf) () (Engine.Term.Context.empty, Commands.Idle)) with
  | (ctx, Commands.Proofmode (_, _, _, g :: _)), () -> print_string (Goal.print g ctx)
  | exception Engine.Term.TypeError (ctx, e) -> print_string (Engine.Term.print_type_error e ctx)
  | exception Kernel.Term.TypeError (ctx, e) -> print_string (Kernel.Term.print_type_error e ctx)
  | exception Commands.Error (ctx, e) -> print_string (Commands.print_error e ctx)
  | exception Parser.Error ->
    let pos = Lexing.lexeme_start_p lexbuf in
    Printf.printf "Syntax error at line %d, column %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
  | exception Term.Error (_, e) -> print_string (Term.print_error e)
  | exception Tactic.Error (ctx, e) -> let e = Tactic.print_error e ctx in print_string e
  | _ -> ()
