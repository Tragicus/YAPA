open Term.Context.Monad.Notations

type univ =
  | Var of string
  | Max of univ list
  | Shift of univ * int

type term =
  | Const of string * string list option
  | Fun of term Term.telescope * term
  | App of term list (* FIXME: slow *)
  | Type of string option
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

let rec capture_vars ictx uctx (t : term) =
  let capture_tele ictx uctx tele k =
    let rec aux ictx uctx tele k revtele =
      match tele with
      | [] -> k ictx uctx (List.rev revtele)
      | (v, t) :: tele ->
        let* t = capture_vars ictx uctx t in
        let** depth = Term.Context.depth in
        let ictx = Utils.SMap.add v depth ictx in
        Term.Context.Monad.with_var (Some v, t, None) (aux ictx uctx tele k ((v, t) :: revtele)) in
    aux ictx uctx tele k [] in
  match t with
  | Type (Some s) -> Term.Context.Monad.ret (Term.Type (if s = "" then Univ.of_atom 0 0 else try Utils.SMap.find s uctx with Not_found -> failwith (String.cat "Unkown universe " s)))
  | Type None -> let+ u = Term.Context.new_univ in Term.Type u
  | App l ->
    let+ l = List.fold_left (fun state t -> let* l = state in let+ t = capture_vars ictx uctx t in t :: l) (Term.Context.Monad.ret []) l in
    Term.App (List.rev l)
  | Const (c, u) ->
    (match Utils.SMap.find c ictx with
    | v ->
      if u <> None then failwith "Local variables do not have universe arguments." else
      Term.Context.Monad.to_mut (
      let+* depth = Term.Context.depth in
      Term.Var (depth - 1 - v))
    | exception _ ->
    let** univ = Term.Context.get_const_univ c in
    let+ newu = match u with
      | None ->
        let+ u = Term.Context.new_univs_with_constraints univ in
        List.map (fun v -> Univ.of_atom v 0) u
      | Some u ->
      if List.length u <> fst (Utils.IMap.max_binding univ) then
        failwith (String.cat "Unexpected number of universe argument for conconstant stant " c) else
      let u = List.map (fun u -> try Utils.SMap.find u uctx with Not_found -> failwith (String.cat "Unknown universe variable " u)) u in
      let+ () = Term.Context.add_univ_constraints (Univ.Context.subst (fun i -> if i = 0 then Univ.static 0 else List.nth u (i-1)) univ) in
      u in
    Term.Const (newu, c))
  | Fun (tele, body) ->
    let+ tele, body = capture_tele ictx uctx tele (fun ictx uctx tele -> let+ t = capture_vars ictx uctx body in tele, t) in
    Term.Fun (tele, body)
  | Pi (tele, body) ->
    let+ tele, body = capture_tele ictx uctx tele (fun ictx uctx tele -> let+ t = capture_vars ictx uctx body in tele, t) in
    Term.Pi (tele, body)
  | Let (v, ty, t, body) ->
    let* ty = capture_vars ictx uctx ty in
    let* t = capture_vars ictx uctx t in
    let** depth = Term.Context.depth in
    let+ body = 
      Term.Context.Monad.with_var (Some v, ty, Some t) (
        capture_vars (Utils.SMap.add v depth ictx) uctx body
      ) in
    Term.Let (v, ty, t, body)
  | Ind (v, a, c) ->
    let* a = capture_vars ictx uctx a in
    let** depth = Term.Context.depth in
    let ictx = Utils.SMap.add v depth ictx in
    let+ c = 
      Term.Context.Monad.with_var (Some v, Term.Var(0), None) (
        let+ l = List.fold_left (fun state t -> let* l = state in let+ t = capture_vars ictx uctx t in t :: l) (Term.Context.Monad.ret []) c in
        List.rev l
      ) in
    Term.Ind (a, c)
  | Construct (ind, i) -> let+ ind = capture_vars ictx uctx ind in Term.Construct (ind, i)
  | Case (ind, r) -> let+ ind = capture_vars ictx uctx ind in Term.Case (ind, r) 

type t =
  | Print of term
  | Check of term
  | Define of string * string list option * term Term.telescope * term * term
  | Whd of term
  | Eval of term
  | Stop

let eval : t -> unit Term.Context.Monad.t = function
  | Print (Const (c, _)) ->
    let** body = Term.Context.get_const_body c in
    let () = print_string c; print_string " := " in
    let** () = Printer.pp_term body in
    Term.Context.Monad.ret (print_newline ())
  | Print _ ->
    failwith "I can only print the body of constants"
  | Check t ->
    let* t = capture_vars Utils.SMap.empty Utils.SMap.empty t in
    let* ty = Term.type_of t in
    let** () = Printer.pp_term t in
    print_string " : ";
    let** () = Printer.pp_term ty in
    fun ctx -> { ctx with Term.univ = Univ.Context.empty }, (print_string "\n")
  | Define (v, u, tele, ty, body) ->
    let** () = fun ctx -> if Term.Context.depth ctx <> 0 then let () = Printer.pp_ctx ctx in failwith "nonempty context" else () in
    let* uctx = match u with
      | None -> Term.Context.Monad.ret (Utils.SMap.empty)
      | Some u ->
      let+ u = Term.Context.Monad.List.map (fun v -> let+ u = Term.Context.new_univ in (v, u)) u in
      List.fold_left (fun uctx (v, u) -> Utils.SMap.add v u uctx) Utils.SMap.empty u in
    let* ty = capture_vars Utils.SMap.empty uctx (mkPi tele ty) in
    let* body = capture_vars Utils.SMap.empty uctx (mkFun tele body) in
    let* tyb = Term.type_of body in
    let* b = Term.unify tyb ty in
    if not b then fun ctx -> raise (Term.TypeError (ctx, Term.TypeMismatch (ty, body))) else
    let* body, tyb = Term.elim_irrelevant_univs body in 
    let** univ = fun ctx -> ctx.Term.univ in
    let* () = Term.Context.push_const v (univ, tyb, body) in
    fun ctx -> { ctx with Term.univ = Univ.Context.empty }, ()
  | Whd t ->
    let* t = capture_vars Utils.SMap.empty Utils.SMap.empty t in
    let** t' = Term.whd t in
    let () = print_string "whd " in
    let** () = Printer.pp_term t in
    let () = print_string " := " in
    let** () = Printer.pp_term t' in
    fun ctx -> { ctx with Term.univ = Univ.Context.empty }, (print_newline ())
  | Eval t ->
    let* t = capture_vars Utils.SMap.empty Utils.SMap.empty t in
    let** t' = Term.eval t in
    let () = print_string "eval " in
    let** () = Printer.pp_term t in
    let () = print_string " := " in
    let** () = Printer.pp_term t' in
    fun ctx -> { ctx with Term.univ = Univ.Context.empty }, (print_newline ())
  | Stop -> failwith "Stop"

