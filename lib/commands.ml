open Term.Context.Monad.Notations

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

let rec capture_vars ictx (t : term) ctx =
  let capture_tele ictx tele k =
    let rec aux ictx tele k revtele =
      match tele with
      | [] ->  Term.Context.Monad.to_mut (k ictx (List.rev revtele))
      | (v, t) :: tele ->
        let** t = capture_vars ictx t in
        let** depth = Term.Context.depth in
        let ictx = Utils.SMap.add v depth ictx in
        Term.Context.Monad.with_var (Some v, t, None) (aux ictx tele k ((v, t) :: revtele)) in
    Term.Context.Monad.to_imut (aux ictx tele k []) in
  match t with
  | Type s -> Term.Type s
  | App l -> Term.App (List.map (fun t -> capture_vars ictx t ctx) l)
  | Const c ->
    (try Var (Term.Context.depth ctx - 1 - Utils.SMap.find c ictx)
    with _ -> Term.Const c)
  | Fun (tele, body) ->
    let tele, body = capture_tele ictx tele (fun ictx tele ctx -> tele, capture_vars ictx body ctx) ctx in
    Term.Fun (tele, body)
  | Pi (tele, body) ->
    let tele, body = capture_tele ictx tele (fun ictx tele ctx -> tele, capture_vars ictx body ctx) ctx in
    Term.Pi (tele, body)
  | Let (v, ty, t, body) ->
    let ty = capture_vars ictx ty ctx in
    let t = capture_vars ictx t ctx in
    let depth = Term.Context.depth ctx in
    let body = Term.Context.Monad.to_imut (
      Term.Context.Monad.with_var (Some v, ty, Some t) (
        Term.Context.Monad.to_mut (
          capture_vars (Utils.SMap.add v depth ictx) body
          )
        )
      ) ctx in
    Term.Let (v, ty, t, body)
  | Ind (v, a, c) ->
    let a = capture_vars ictx a ctx in
    let ictx = Utils.SMap.add v (Term.Context.depth ctx) ictx in
    let c = Term.Context.Monad.to_imut (
      Term.Context.Monad.with_var (Some v, Term.Var(0), None) (
        Term.Context.Monad.to_mut (fun ctx ->
          List.map (fun t -> capture_vars ictx t ctx) c
        )
      )
    ) ctx in
    Term.Ind (a, c)
  | Construct (ind, i) -> Term.Construct (capture_vars ictx ind ctx, i)
  | Case (ind, r) -> Term.Case (capture_vars ictx ind ctx, r) 

type t =
  | Print of term
  | Check of term
  | Define of string * term Term.telescope * term * term
  | Whd of term
  | Eval of term
  | Stop

let eval = function
  | Print (Const c) ->
    let** body = Term.Context.get_const_body c in
    let () = print_string c; print_string " := " in
    let** () = Printer.pp_term body in
    Term.Context.Monad.ret (print_newline ())
  | Print _ ->
    failwith "I can only print the body of constants"
  | Check t ->
    let** t = capture_vars Utils.SMap.empty t in
    let* ty = Term.type_of t in
    let** () = Printer.pp_term t in
    print_string " : ";
    let** () = Printer.pp_term ty in
    Term.Context.Monad.ret (print_newline ())
  | Define (v, tele, ty, body) ->
    let** () = fun ctx -> if Term.Context.depth ctx <> 0 then let () = Printer.pp_ctx ctx in failwith "nonempty context" else () in
    let** ty = capture_vars Utils.SMap.empty (mkPi tele ty) in
    let** body = capture_vars Utils.SMap.empty (mkFun tele body) in
    let* tyb = Term.type_of body in
    let* b = Term.unify tyb ty in
    if b then Term.Context.push_const v (ty, body)
      else fun ctx -> raise (Term.TypeError (ctx, Term.TypeMismatch (ty, body)))
  | Whd t ->
    let** t = capture_vars Utils.SMap.empty t in
    let** t' = Term.whd t in
    let () = print_string "whd " in
    let** () = Printer.pp_term t in
    let () = print_string " := " in
    let** () = Printer.pp_term t' in
    Term.Context.Monad.ret (print_newline ())
  | Eval t ->
    let** t = capture_vars Utils.SMap.empty t in
    let** t' = Term.eval t in
    let () = print_string "eval " in
    let** () = Printer.pp_term t in
    let () = print_string " := " in
    let** () = Printer.pp_term t' in
    Term.Context.Monad.ret (print_newline ())
  | Stop -> failwith "Stop"

