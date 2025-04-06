type univ=
  | Var of string
  | Max of univ list
  | Shift of univ * int

type term =
  | Const of string
  | Fun of term Term.telescope * term
  | App of term list (* FIXME: slow *)
  | Type of Univ.t option
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
      let ctx, t = capture_vars ictx ctx t in
      Utils.SMap.add v (Term.Context.depth ctx) ictx, Term.Context.push_var (Some v, t, None) ctx, (v, t) :: tele) (ictx, ctx, []) tele in
    ictx, ctx, List.rev tele in
  (*let capture_univ = function
    | Var v -> Univ.of_atom (SMap.find v) 0
    | Max us ->
      List.fold_left (fun g u -> Univ.max g (capture_univ u)) IMap.empty us
    | Shift (u, i) -> Univ.shift i u in *)
  match t with
  | Type (Some s) -> ctx, Term.Type s
  | Type None ->
    let ctx, u = Term.Context.new_univ ctx in
    ctx, Term.Type u
  | App l ->
    let ctx, l = List.fold_left_map (capture_vars ictx) ctx l in
    ctx, Term.App l
  | Const c ->
    (try ctx, Var (Term.Context.depth ctx - 1 - Utils.SMap.find c ictx)
    with _ ->
    let univ = Term.Context.get_const_univ ctx c in
    let ctx, newu = Term.Context.new_univs_with_constraints univ ctx in
    ctx, Term.Const (List.map (fun v -> Univ.of_atom v 0) newu, c))
  | Fun (tele, body) ->
    let ictx, ctx', tele = capture_tele ictx ctx tele in
    let ctx', body = capture_vars ictx ctx' body in
    { ctx with univ = ctx'.univ }, Term.Fun (tele, body)
  | Pi (tele, body) ->
    let ictx, ctx', tele = capture_tele ictx ctx tele in
    let ctx', body = capture_vars ictx ctx' body in
    { ctx with univ = ctx'.univ }, Term.Pi (tele, body)
  | Let (v, ty, t, body) ->
    let ctx, ty = capture_vars ictx ctx ty in
    let ctx, t = capture_vars ictx ctx t in
    let ctx', body = capture_vars (Utils.SMap.add v (Term.Context.depth ctx) ictx) (Term.Context.push_var (Some v, ty, Some t) ctx) body in
    { ctx with univ = ctx'.univ }, Term.Let (v, ty, t, body)
  | Ind (v, a, c) ->
    let ctx, a = capture_vars ictx ctx a in
    let ictx = Utils.SMap.add v (Term.Context.depth ctx) ictx in
    let ctx' = Term.Context.push_var (Some v, Term.Var(0), None) ctx in
    let ctx', c = List.fold_left_map (capture_vars ictx) ctx' c in
    { ctx with univ = ctx'.univ }, Term.Ind (a, c)
  | Construct (ind, i) ->
    let ctx, ind = capture_vars ictx ctx ind in
    ctx, Term.Construct (ind, i)
  | Case (ind, r) ->
    let ctx, ind = capture_vars ictx ctx ind in
    ctx, Term.Case (ind, r) 

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
    let ctx', t = capture_vars Utils.SMap.empty ctx t in
    let () = Printer.pp_term ctx' t; print_string " : " in
    let ctx', ty = Term.type_of ctx' t in
    let () = Printer.pp_term ctx' ty in
    let () = print_string "\n" in
    ctx
  | Define (v, tele, ty, body) ->
    let ctx, ty = capture_vars Utils.SMap.empty ctx (mkPi tele ty) in
    let ctx, body = capture_vars Utils.SMap.empty ctx (mkFun tele body) in
    let ctx, tybody = Term.type_of ctx body in
    if not (Term.unify ctx tybody ty)
      then raise (Term.TypeError (ctx, Term.TypeMismatch (ty, body))) else
    let ctx = Term.Context.push_const v (ctx.univ, ty, body) ctx in
    { ctx with univ = Univ.Context.empty }
  | Whd t ->
    let ctx', t = capture_vars Utils.SMap.empty ctx t in
    let () = print_string "whd "; Printer.pp_term ctx' t; print_string " := " in
    let () = Printer.pp_term ctx' (Term.whd ctx' t) in
    let () = print_newline () in
    ctx
  | Eval t ->
    let ctx', t = capture_vars Utils.SMap.empty ctx t in
    let () = print_string "eval "; Printer.pp_term ctx' t; print_string " := " in
    let () = Printer.pp_term ctx' (Term.eval ctx' t) in
    let () = print_newline () in
    ctx
  | Stop -> failwith "Stop"

