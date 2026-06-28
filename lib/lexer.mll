{
  open Parser

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c
}

let backslash_escapes =
    ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']

rule token = parse
  | eof { EOF }
  | [' ' '\t']+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | ['0'-'9']+ as s { INT (int_of_string s) }
  | '"' { string [] lexbuf }
  | '(' { LPAR }
  | ')' { RPAR }
  | '{' { LCBRACE }
  | '}' { RCBRACE }
  | "fun" { FUN }
  | "=>" { ARROW }
  | "->" { TARROW }
  | "let" { LET }
  | "in" { IN }
  | "forall" { FORALL }
  | "Type" { TYPE }
  | "Prop" { PROP }
  | "SProp" { SPROP }
  | "ind" { IND }
  | "|" { PIPE }
  | "match" { MATCH }
  | "rec" { REC }
  | "with" { WITH }
  | "return" { RETURN }
  | "end" { END }
  | ".mk" { MK }
  | "Print" { PRINT }
  | "Check" { CHECK }
  | "Definition" { DEF }
  | "Proof" { PROOF }
  | "Whd" { WHD }
  | "Eval" { EVAL }
  | "Set" { SET }
  | "Unset" { UNSET }
  | "Stop" { STOP }
  | "exact" { EXACT }
  | "refine" { REFINE }
  | "apply" { APPLY }
  | "intros" { INTRO }
  | "intro" { INTRO }
  | "clear" { CLEAR }
  | "assumption" { ASSUMPTION }
  | "auto" { AUTO }
  | "Qed" { QED }
  | "Defined" { DEFINED }
  | "Hint" { HINT }
  | "for" { FOR }
  | "," { COMMA }
  | "." { DOT }
  | ":" { COLON }
  | ";" { SCOLON }
  | ":=" { COLONEQ }
  | '@' { AT }
  | '_' { HOLE }
  | ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as s { VAR s }
  | _  { failwith "lexical error" }

and string acc = parse
  | '"' { STRING (String.of_seq (List.to_seq (List.rev acc))) }
  | '\\' (backslash_escapes as c) { string ((char_for_backslash c) :: acc) lexbuf }
  | _ as c { string (c :: acc) lexbuf }
