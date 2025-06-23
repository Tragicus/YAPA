%token <int> INT
%token <string> VAR
%token EOF
%token LPAR RPAR LCBRACE RCBRACE FUN ARROW
%token LET IN FORALL TARROW COMMA DOT COLON COLONEQ AT HOLE
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
  (*open Utils*)

%}

%%

toplevel:
  | list(command); EOF { $1 }

univ_annot:
  | AT; LCBRACE; VAR; RCBRACE { $3 }

univ_annots:
  | AT; LCBRACE; separated_list(COMMA, VAR); RCBRACE { $3 }

command:
  | PRINT; term; DOT { Commands.Print $2 }
  | CHECK; term; DOT { Commands.Check $2 }
  | DEF; VAR; option(univ_annots); telescope; option(type_annotation); COLONEQ; term; DOT { Commands.Define ($2, $3, $4, Option.value ~default:Commands.THole $5, $7) }
  | WHD; term; DOT { Commands.Whd $2 }
  | EVAL; term; DOT { Commands.Eval $2 }

type_annotation:
  | COLON; term { $2 }

match_return:
  | RETURN; term {$2}

term:
  | FUN; telescope; ARROW; term { Commands.mkFun $2 $4 }
  | FORALL; telescope; COMMA; term { Commands.mkPi $2 $4 }
  | LET; VAR; COLON; term; COLONEQ; term; IN; term { Commands.Let ($2, $4, $6, $8) }
  | IND; VAR; option(type_annotation); constructors; END { Commands.Ind ($2, Option.value ~default:Commands.THole $3, $4) }
  | MATCH; option(REC); term; option(type_annotation); option(match_return); WITH; constructors; END { (Commands.Case ($2 <> None, $3, $4, Option.value ~default:Commands.Hole $5, $7)) }
  | term; TARROW; term { Commands.mkPi [("_", $1)] $3 }
  | app { $1 }

telescope_elem:
  | LPAR; nonempty_list(VAR); COLON; term; RPAR { List.map (fun x -> (x, $4)) $2 }
  | VAR { [$1, Commands.THole] }

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
  | VAR; option(univ_annots) { Commands.Const($1, $2) }
  | TYPE; option(univ_annot) { Commands.Type $2 }
  | PROP { Commands.Type (Some "") }
  | HOLE { Commands.Hole }
  | LPAR; term; RPAR { $2 }
  | sterm; MK; INT { Commands.Construct ($1, $3) }
