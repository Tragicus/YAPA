{
  open Parser
}

rule token = parse
  | eof { EOF }
  | [' ' '\t']+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | ['0'-'9']+ as s { INT (int_of_string s) }
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
  | "Whd" { WHD }
  | "Eval" { EVAL }
  | "," { COMMA }
  | "." { DOT }
  | ":" { COLON }
  | ":=" { COLONEQ }
  | '@' { AT }
  | '_' { HOLE }
  | ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']* as s { VAR s }
  | _  { failwith "lexical error" }
