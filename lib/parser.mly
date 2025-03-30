%token <int> INT
%token <string> VAR
%token EOF
%token LPAR RPAR FUN ARROW
%token LET IN FORALL TARROW COMMA DOT JOKER COLON COLONEQ
%token TYPE PROP
%token IND PIPE MATCH REC WITH RETURN END MK
%token PRINT CHECK DEF WHD EVAL

%nonassoc COMMA
%nonassoc ARROW
%nonassoc IN
%right TARROW

%start <Commands.t list> toplevel
%type <Commands.term> term
%type <Commands.term list> constructors
%type <Commands.term> sterm

%{
  open Utils

%}

%%

toplevel:
  | list(command); EOF { $1 }

command:
  | PRINT; term; DOT { Commands.Print $2 }
  | CHECK; term; DOT { Commands.Check $2 }
  | DEF; VAR; COLON; term; COLONEQ; term; DOT { Commands.Define ($2, $4, $6) }
  | WHD; term; DOT { Commands.Whd $2 }
  | EVAL; term; DOT { Commands.Eval $2 }

term:
  | FUN; telescope; ARROW; term { Commands.mkFun $2 $4 }
  | FORALL; telescope; COMMA; term { Commands.mkPi $2 $4 }
  | LET; VAR; COLON; term; COLONEQ; term; IN; term { Commands.Let ($2, $4, $6, $8) }
  | IND; VAR; COLON; term; constructors; END { Commands.Ind ($2, $4, $5) }
  | MATCH; option(REC); term; COLON; term; RETURN; term; WITH; constructors; END { Commands.App ((Commands.Case ($5, $2 <> None)) :: $7 :: $9 @ [$3]) }
  | term; TARROW; term { Commands.mkPi [("_", $1)] $3 }
  | app { $1 }

telescope_elem:
  | LPAR; nonempty_list(VAR); COLON; term; RPAR { List.map (fun x -> (x, $4)) $2 }

%inline
telescope:
  | list(telescope_elem) { List.flatten $1 }

%inline
constructors:
  | list(preceded(PIPE, term)) { $1 }
  
%inline
app:
  | nonempty_list(sterm) { match $1 with | [] -> Commands.App [] | e :: l -> Commands.mkApp e l }

sterm:
  | VAR { Commands.Const $1 }
  | TYPE { Commands.Type (SMap.singleton "" 1) }
  | PROP { Commands.Type (SMap.singleton "" 0) }
  | LPAR; term; RPAR { $2 }
  | sterm; MK; INT { Commands.Construct ($1, $3) }
