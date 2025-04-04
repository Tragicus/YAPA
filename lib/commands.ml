type term =
  | Const of string
  | Fun of term Term.telescope * term
  | App of term list (* FIXME: slow *)
  | Type of Univ.t
  | Pi of term Term.telescope * term
  | Let of string * term * term * term
  | Ind of (* name *) string * (* arity *) term * (* constructors *) term list
  | Construct of term * int
  | Case of (* inductive *) term * (* recursive *) bool

let destApp = function
  | App (f :: args) -> f, args
  | f -> f, []

let mkApp f args =
  if args = [] then f else
  let f, fargs = destApp f in
  App (f :: fargs @ args)

let mkFun f body =
  if f = [] then body else
  match body with
  | Fun (tele, body) -> Fun (f @ tele, body)
  | _ -> Fun (f, body)

let mkPi f body =
  if f = [] then body else
  match body with
  | Pi (tele, body) -> Pi (f @ tele, body)
  | _ -> Pi (f, body)

let rec capture_vars ictx ctx t =
  let capture_tele ictx ctx tele =
    let ictx, ctx, tele = List.fold_left (fun (ictx, ctx, tele) (v, t) ->
      let t = capture_vars ictx ctx t in
      Utils.SMap.add v (Term.Context.depth ctx) ictx, Term.Context.push_var (Some v, t, None) ctx, (v, t) :: tele) (ictx, ctx, []) tele in
    ictx, ctx, List.rev tele in
  match t with
  | Type s -> Term.Type s
  | App l -> Term.App (List.map (capture_vars ictx ctx) l)
  | Const c ->
    (try Var (Term.Context.depth ctx - 1 - Utils.SMap.find c ictx)
    with _ -> Term.Const c)
  | Fun (tele, body) ->
    let ictx, ctx, tele = capture_tele ictx ctx tele in
    Term.Fun (tele, capture_vars ictx ctx body)
  | Pi (tele, body) ->
    let ictx, ctx, tele = capture_tele ictx ctx tele in
    Term.Pi (tele, capture_vars ictx ctx body)
  | Let (v, ty, t, body) ->
    let ty = capture_vars ictx ctx ty in
    let t = capture_vars ictx ctx t in
    Term.Let (v, ty, t, capture_vars (Utils.SMap.add v (Term.Context.depth ctx) ictx) (Term.Context.push_var (Some v, ty, Some t) ctx) body)
  | Ind (v, a, c) ->
    let a = capture_vars ictx ctx a in
    let ictx = Utils.SMap.add v (Term.Context.depth ctx) ictx in
    let ctx = Term.Context.push_var (Some v, Term.Var(0), None) ctx in
    Term.Ind (a, List.map (capture_vars ictx ctx) c)
  | Construct (ind, i) -> Term.Construct (capture_vars ictx ctx ind, i)
  | Case (ind, r) -> Term.Case (capture_vars ictx ctx ind, r) 

type t =
  | Print of term
  | Check of term
  | Define of string * term Term.telescope * term * term
  | Whd of term
  | Eval of term
  | Stop

let eval ctx = function
  | Print (Const c) ->
    let () = print_string c; print_string " := " in
    let () = Printer.pp_term ctx (Term.Context.get_const_body ctx c) in
    let () = print_newline () in
    ctx
  | Print _ ->
    failwith "I can only print the body of constants"
  | Check t ->
    let t = capture_vars Utils.SMap.empty ctx t in
    let () = Printer.pp_term ctx t; print_string " : " in
    let () = Printer.pp_term ctx (Term.type_of ctx t) in
    let () = print_newline () in
    ctx
  | Define (v, tele, ty, body) ->
    let ty = capture_vars Utils.SMap.empty ctx (mkPi tele ty) in
    let body = capture_vars Utils.SMap.empty ctx (mkFun tele body) in
    if Term.unify ctx (Term.type_of ctx body) ty 
      then Term.Context.push_const v (ty, body) ctx
    else raise (Term.TypeError (ctx, Term.TypeMismatch (ty, body)))
  | Whd t ->
    let t = capture_vars Utils.SMap.empty ctx t in
    let () = print_string "whd "; Printer.pp_term ctx t; print_string " := " in
    let () = Printer.pp_term ctx (Term.whd ctx t) in
    let () = print_newline () in
    ctx
  | Eval t ->
    let t = capture_vars Utils.SMap.empty ctx t in
    let () = print_string "eval "; Printer.pp_term ctx t; print_string " := " in
    let () = Printer.pp_term ctx (Term.eval ctx t) in
    let () = print_newline () in
    ctx
  | Stop -> ctx

