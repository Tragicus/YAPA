%token <int> INT
%token <string> VAR
%token EOF
%token LPAR RPAR FUN ARROW
%token LET IN FORALL TARROW COMMA DOT JOKER COLON COLONEQ
%token TYPE PROP
%token PRINT CHECK DEF

%nonassoc COMMA
%nonassoc ARROW
%nonassoc IN
%right TARROW

%start <Commands.t list> toplevel
%type <Term.t> term
%type <Term.t list> revstermlist
%type <Term.t> sterm

%{
  open Utils
  open Term

  let rec mkAbstraction constructor e = function
  | [] -> e
  | (v, t) :: l -> constructor (v, t, mkAbstraction constructor e l)

  let rec capture_vars ctx level t =
  match t with
  | Var _ | Type _ -> t
  | App l -> App (List.map (capture_vars ctx level) l)
  | Const c ->
    (try Var (level - SMap.find c ctx - 1)
    with _ -> t)
  | Fun (v, t, body) ->
    Fun (v, capture_vars ctx level t, capture_vars (SMap.add v level ctx) (level + 1) body)
  | Pi (v, t, body) ->
    Pi (v, capture_vars ctx level t, capture_vars (SMap.add v level ctx) (level + 1) body)
  | Let (v, ty, t, body) ->
    Let (v, capture_vars ctx level ty, capture_vars ctx level t, capture_vars (SMap.add v level ctx) (level + 1) body)
%}

%%

toplevel:
  | revcommands; EOF { List.rev $1 }

command:
  | PRINT; toplevel_term; DOT { Commands.Print $2 }
  | CHECK; toplevel_term; DOT { Commands.Check $2 }
  | DEF; VAR; COLON; toplevel_term; COLONEQ; toplevel_term; DOT { Commands.Define ($2, $4, $6) }

revcommands:
  | revcommands; command { $2 :: $1 }
  | command { [$1] }

toplevel_term:
  | term { capture_vars SMap.empty 0 $1 }

term:
  | FUN; revtelescope; ARROW; term { mkAbstraction (function (x, y, z) -> Term.Fun (x, y, z)) $4 (List.rev $2) }
  | FORALL; revtelescope; COMMA; term { mkAbstraction (function (x, y, z) -> Term.Pi (x, y, z)) $4 (List.rev $2) }
  | LET; VAR; COLON; term; COLONEQ; term; IN; term { Term.Let ($2, $4, $6, $8)}
  | term; TARROW; term { mkAbstraction (function (x, y, z) -> Term.Pi (x, y, z)) $3 [("_", $1)] }
  | app { $1 }

revvarlist:
  | revvarlist; VAR { $2 :: $1 }
  | VAR { [$1] }

revtelescope_elem:
  | LPAR; revvarlist; COLON; term; RPAR { List.map (fun x -> (x, $4)) $2 }

revtelescope:
  | revtelescope; revtelescope_elem { List.append $2 $1 }
  | revtelescope_elem { $1 }

app:
  | revstermlist { match $1 with | [e] -> e | l -> Term.App (List.rev l) }

revstermlist:
  | revstermlist; sterm { $2 :: $1 }
  | sterm { [$1] }

sterm:
  | VAR { Term.Const $1 }
  | TYPE { Term.Type 1 }
  | PROP { Term.Type 0 }
  | LPAR; term; RPAR { $2 }
