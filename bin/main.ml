open Yapa
open Utils

let () =
  let () = Random.init 0 in
  let file = ref "" in
  let () = Arg.parse [] (fun s -> file := s) "" in
  let () = if !file = "" then () else if Filename.extension !file <> ".v" then failwith "Expected .v file" else () in
  let lexbuf = Lexing.from_channel (if !file = "" then Stdlib.stdin else open_in !file) in
  let () = Tactic.parse_hint := fun hint ->
    Parser.toptactic Lexer.token (Lexing.from_string (hint ^ ".")) in
  try
    let _, serialized = Commands.Context.Monad.List.fold_left Commands.Context.Monad.Notations.(fun c acc ->
        let+ r = Commands.eval c in
        match r with | None -> acc | Some s -> s :: acc
      ) (Parser.toplevel Lexer.token lexbuf) [] (Engine.Term.Context.empty, Commands.Idle) in
    if !file = "" then () else
    let file = Filename.remove_extension !file in
    let file = file ^ ".vo" in
    let json = List.to_json (function
      | Commands.Serialized.Define (v, u, ty, body) -> `Assoc [ ("name", String.to_json v); ("univ", Kernel.Univ.Context.to_json u); ("type", Kernel.Term.to_json ty); ("body", Option.to_json Kernel.Term.to_json body) ]
      | Commands.Serialized.Hint (pat, tac) -> `Assoc [ ("pattern", Engine.Pattern.to_json pat); ("tactic", String.to_json tac) ]) (List.rev serialized) in
    Yojson.Basic.to_file file json
  with
  | Engine.Term.TypeError (ctx, e) -> print_string (Engine.Term.print_type_error e ctx)
  | Kernel.Term.TypeError (ctx, e) -> print_string (Kernel.Term.print_type_error e ctx)
  | Commands.Error (ctx, e) -> print_string (Commands.print_error e ctx)
  | Parser.Error ->
    let pos = Lexing.lexeme_start_p lexbuf in
    Printf.printf "Syntax error at line %d, column %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
  | Term.Error (_, e) -> print_string (Term.print_error e)
  | Tactic.Error (ctx, e) -> let e = Tactic.print_error e ctx in print_string e
