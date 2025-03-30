{
  open Parser
}

rule token = parse
  | eof { EOF }
  | [' ' '\t' '\n']+ { token lexbuf }
  | ['0'-'9']+ as s { INT (int_of_string s) }
  | '(' { LPAR }
  | ')' { RPAR }
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
  | "with" { WITH }
  | "return" { RETURN }
  | "end" { END }
  | ".mk" { MK }
  | "Print" { PRINT }
  | "Check" { CHECK }
  | "Definition" { DEF }
  | "," { COMMA }
  | "." { DOT }
  | "_" { JOKER }
  | ":" { COLON }
  | ":=" { COLONEQ }
  | ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']* as s { VAR s }
  | _  { failwith "lexical error" }
