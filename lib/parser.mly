%token <int> INT
%token <string> VAR
%token EOF
%token LPAR RPAR LCBRACE RCBRACE FUN ARROW
%token LET IN FORALL TARROW COMMA DOT COLON SCOLON COLONEQ AT HOLE
%token TYPE PROP SPROP
%token IND PIPE MATCH REC WITH RETURN END MK
%token PRINT CHECK DEF PROOF WHD EVAL STOP
%token EXACT REFINE APPLY INTRO CLEAR ASSUMPTION
%token QED DEFINED

%nonassoc COMMA
%nonassoc ARROW
%nonassoc IN
%right TARROW

%start <Commands.t list> toplevel
%type <Term.t> term
%type <Term.t list> constructors
%type <Term.t> sterm
%type <Tactic.t> tac

%{
  (*open Utils*)

%}

%%

toplevel:
  | list(command); EOF { $1 }

univ_annot:
  | AT; LCBRACE; VAR; SCOLON; VAR RCBRACE { $3, Utils.SMap.singleton $5 0 }

univ_annots:
  | AT; LCBRACE; separated_list(COMMA, VAR); SCOLON; separated_list(COMMA, VAR); RCBRACE { $3, List.map (fun u -> Utils.SMap.singleton u 0) $5 }

univ_decls:
  | AT; LCBRACE; separated_list(COMMA, VAR); SCOLON; separated_list(COMMA, VAR); RCBRACE { $3, $5 }

command:
  | PRINT; term; DOT { Commands.Print $2 }
  | CHECK; term; DOT { Commands.Check $2 }
  | DEF; VAR; option(univ_decls); telescope; option(type_annotation); option(body_annotation); DOT { Commands.Define ($2, $3, Term.mkForall $4 (Option.value ~default:(Term.of_hd (Term.Evar "_")) $5), Term.mkFun $4 (Option.value ~default:(Term.of_hd (Term.Evar "_")) $6)) }
  | PROOF; DOT { Commands.Skip }
  | WHD; term; DOT { Commands.Whd $2 }
  | EVAL; term; DOT { Commands.Eval $2 }
  | QED; DOT { Commands.Qed false }
  | DEFINED; DOT { Commands.Qed true }
  | STOP; DOT { Commands.Stop }
  | tac; DOT { Commands.Tac $1 }

tac:
  | separated_list(SCOLON, tac_atom) { match $1 with | [] -> failwith "unreachable" | [t] -> t | l -> Tactic.Seq l }

tac_atom:
  | EXACT; term { Tactic.Exact $2 }
  | REFINE; term { Tactic.Refine $2 }
  | APPLY; separated_list(COMMA, term) { Tactic.Apply $2 }
  | INTRO; list(VAR) { Tactic.Intro $2 }
  | CLEAR; list(VAR) { Tactic.Clear $2 }
  | ASSUMPTION { Tactic.Assumption }
  | LPAR; tac; RPAR { $2 }

type_annotation:
  | COLON; term { $2 }
body_annotation:
  | COLONEQ; term { $2 }

match_return:
  | RETURN; term {$2}

term:
  | FUN; telescope; ARROW; term { Term.mkFun $2 $4 }
  | FORALL; telescope; COMMA; term { Term.mkForall $2 $4 }
  | LET; VAR; COLON; term; COLONEQ; term; IN; term { Term.mkFun [($2, $4, Some $6)] $8 }
  | IND; VAR; option(type_annotation); constructors; END { Term.mkInd $2 (Option.value ~default:(Term.of_hd (Term.Evar "_")) $3) $4 }
  | MATCH; option(REC); term; option(type_annotation); option(match_return); WITH; list(preceded(PIPE, branch)); END { Term.mkCase ($2 <> None) $3 $4 (Option.value ~default:(Term.of_hd (Term.Evar "_")) $5) $7 }
  | term; TARROW; term { Term.mkForall [("_", $1, None)] $3 }
  | app { $1 }

telescope_elem:
  | LPAR; nonempty_list(VAR); COLON; term; RPAR { List.map (fun x -> (x, $4, None)) $2 }
  | VAR { [$1, Term.of_hd (Term.Evar " "), None] }

%inline
telescope:
  | list(telescope_elem) { List.flatten $1 }

%inline
constructors:
  | list(preceded(PIPE, term)) { $1 }

%inline
branch:
  | term; ARROW; term { ($1, $3) }
  
%inline
app:
  | nonempty_list(sterm) { match $1 with | [] -> assert false | e :: l -> Term.mkApp l e }

sterm:
  | VAR; option(univ_annots) { Term.mkConst $1 $2 }
  | TYPE; option(univ_annot) { let (s, u) = Option.value ~default:("_", Utils.SMap.singleton "_" 0) $2 in Term.mkType s u }
  | PROP { Term.mkType "Prop" (Utils.SMap.singleton "_" 0) }
  | SPROP { Term.mkType "SProp" (Utils.SMap.singleton "_" 0) }
  | HOLE { Term.of_hd (Term.Evar "_") }
  | LPAR; term; RPAR { $2 }
  | sterm; MK; LPAR; INT; RPAR { Term.mkConstruct $1 $4 }
