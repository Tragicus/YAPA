open Engine.Term.Context.Monad.Notations

type univ =
  | Var of string
  | Max of univ list
  | Shift of univ * int

type term =
  | Const of string * string list option
  | Fun of term Engine.Term.telescope * term
  | App of term list (* FIXME: slow *)
  | Type of string option
  | Pi of term Engine.Term.telescope * term
  | Let of string * term * term * term
  | Ind of (* name *) string * (* arity *) term * (* constructors *) term list
  | Construct of term * int
  | Case of (* recursive *) bool *
            (* subject *) term *
            (* inductive *) term option *
            (* return type *) term * 
            (* branches *) term list
  | THole
  | Hole

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

let rec elaborate ?(ictx=Utils.SMap.empty) ?(uctx=Utils.SMap.empty) (t : term) =
  let capture_tele ictx uctx tele k =
    let rec aux ictx uctx tele k revtele =
      match tele with
      | [] -> k ictx uctx (List.rev revtele)
      | (v, t) :: tele ->
        let* t = elaborate ~ictx ~uctx t in
        let** depth = Engine.Term.Context.depth in
        let ictx = Utils.SMap.add v depth ictx in
        Engine.Term.Context.Monad.with_var (Some v, t, None) (aux ictx uctx tele k ((v, t) :: revtele)) in
    aux ictx uctx tele k [] in
  match t with
  | Type (Some s) -> Engine.Term.Context.Monad.ret (Engine.Term.Type (if s = "" then Kernel.Univ.of_atom 0 0 else try Utils.SMap.find s uctx with Not_found -> failwith (String.cat "Unkown universe " s)))
  | Type None -> let+ u = Engine.Term.Context.new_univ in Engine.Term.Type u
  | App l ->
    let+ l = List.fold_left (fun state t -> let* l = state in let+ t = elaborate ~ictx ~uctx t in t :: l) (Engine.Term.Context.Monad.ret []) l in
    Engine.Term.App (List.rev l)
  | Const (c, u) ->
    (match Utils.SMap.find c ictx with
    | v ->
      if u <> None then failwith "Local variables do not have universe arguments." else
      Engine.Term.Context.Monad.to_mut (
      let+* depth = Engine.Term.Context.depth in
      Engine.Term.Var (depth - 1 - v))
    | exception _ ->
    let** univ = Engine.Term.Context.get_const_univ c in
    let+ newu = match u with
      | None ->
        let+ u = Engine.Term.Context.new_univs_with_constraints univ in
        List.map (fun v -> Kernel.Univ.of_atom v 0) u
      | Some u ->
      if List.length u <> fst (Utils.IMap.max_binding univ) then
        failwith (String.cat "Unexpected number of universe argument for conconstant stant " c) else
      let u = List.map (fun u -> try Utils.SMap.find u uctx with Not_found -> failwith (String.cat "Unknown universe variable " u)) u in
      let+ () = Engine.Term.Context.add_univ_constraints (Kernel.Univ.Context.subst (fun i -> if i = 0 then Kernel.Univ.static 0 else List.nth u (i-1)) univ) in
      u in
    Engine.Term.Const (newu, c))
  | Fun (tele, body) ->
    let+ tele, body = capture_tele ictx uctx tele (fun ictx uctx tele -> let+ t = elaborate ~ictx ~uctx body in tele, t) in
    Engine.Term.Fun (tele, body)
  | Pi (tele, body) ->
    let+ tele, body = capture_tele ictx uctx tele (fun ictx uctx tele -> let+ t = elaborate ~ictx ~uctx body in tele, t) in
    Engine.Term.Pi (tele, body)
  | Let (v, ty, t, body) ->
    let* ty = elaborate ~ictx ~uctx ty in
    let* t = elaborate ~ictx ~uctx t in
    let** depth = Engine.Term.Context.depth in
    let+ body = 
      Engine.Term.Context.Monad.with_var (Some v, ty, Some t) (
        elaborate ~ictx:(Utils.SMap.add v depth ictx) ~uctx body
      ) in
    Engine.Term.Let (v, ty, t, body)
  | Ind (v, a, c) ->
    let* a = elaborate ~ictx ~uctx a in
    let** depth = Engine.Term.Context.depth in
    let ictx = Utils.SMap.add v depth ictx in
    let+ c = 
      Engine.Term.Context.Monad.with_var (Some v, Engine.Term.Var(0), None) (
        let+ l = List.fold_left (fun state t -> let* l = state in let+ t = elaborate ~ictx ~uctx t in t :: l) (Engine.Term.Context.Monad.ret []) c in
        List.rev l
      ) in
    Engine.Term.Ind (a, c)
  | Construct (ind, i) -> let+ ind = elaborate ~ictx ~uctx ind in Engine.Term.Construct (ind, i)
  | Case (r, s, ind, ret, br) ->
    let* s = elaborate ~ictx ~uctx s in
    let* ind = match ind with | None -> Engine.Term.typecheck s | Some ind -> elaborate ~ictx ~uctx ind in
    let* ret = elaborate ~ictx ~uctx ret in
    let* br = Engine.Term.Context.Monad.List.map (elaborate ~ictx ~uctx) br in
    let+ ind =
      try 
        let** whind = Engine.Term.whd ind in
        let _ =  Engine.Term.destInd whind in
        Engine.Term.Context.Monad.ret ind
      with _ -> 
        let* a = Engine.Term.Context.new_type_evar in
        let* c = Engine.Term.Context.Monad.List.map (fun _ -> Engine.Term.Context.new_type_evar) br in
        Engine.Term.Context.Monad.ret (Engine.Term.Ind (a, c)) in
    Engine.Term.mkApp (Engine.Term.Case (ind, r)) (ret :: br @ [s])
  | THole -> let+ t = Engine.Term.Context.new_type_evar in t
  | Hole -> let+ t = Engine.Term.Context.new_evar in t

type t =
  | Print of term
  | Check of term
  | Define of string * string list option * term Engine.Term.telescope * term * term
  | Whd of term
  | Eval of term
  | Stop

let eval : t -> unit Engine.Term.Context.Monad.t = function
  | Print (Const (c, _)) ->
    let** body = Engine.Term.Context.get_const_body c in
    let () = print_string c; print_string " := " in
    let** () = Printer.Engine.pp_term body in
    Engine.Term.Context.Monad.ret (print_newline ())
  | Print _ ->
    failwith "I can only print the body of constants"
  | Check t ->
    let* t = elaborate t in
    let* ty = Engine.Term.typecheck t in
    let** () = Printer.Engine.pp_term t in
    print_string " : ";
    let** () = Printer.Engine.pp_term ty in
    fun ctx -> { ctx with Engine.Term.univ = Kernel.Univ.Context.empty }, (print_string "\n")
  | Define (v, u, tele, ty, body) ->
    let** () = fun ctx -> if Engine.Term.Context.depth ctx <> 0 then let () = Printer.Engine.pp_ctx ctx in failwith "nonempty context" else () in
    let* uctx = match u with
      | None -> Engine.Term.Context.Monad.ret (Utils.SMap.empty)
      | Some u ->
      let+ u = Engine.Term.Context.Monad.List.map (fun v -> let+ u = Engine.Term.Context.new_univ in (v, u)) u in
      List.fold_left (fun uctx (v, u) -> Utils.SMap.add v u uctx) Utils.SMap.empty u in
    let* ty = elaborate ~uctx (mkPi tele ty) in
    let* body = elaborate ~uctx (mkFun tele body) in
    let* tyb = Engine.Term.typecheck body in
    let* b = Engine.Term.unify tyb ty in
    if not b then fun ctx -> raise (Engine.Term.TypeError (ctx, Engine.Term.TypeMismatch (ty, body))) else
    let* body, tyb = Engine.Term.elim_irrelevant_univs body in 
    let** univ = fun ctx -> ctx.Engine.Term.univ in
    let* () = Engine.Term.Context.push_const v (univ, tyb, body) in
    fun ctx -> { ctx with Engine.Term.univ = Kernel.Univ.Context.empty; Engine.Term.evar = Utils.IMap.empty }, ()
  | Whd t ->
    let* t = elaborate t in
    let** t' = Engine.Term.whd t in
    let () = print_string "whd " in
    let** () = Printer.Engine.pp_term t in
    let () = print_string " := " in
    let** () = Printer.Engine.pp_term t' in
    fun ctx -> { ctx with Engine.Term.univ = Kernel.Univ.Context.empty }, (print_newline ())
  | Eval t ->
    let* t = elaborate t in
    let** t' = Engine.Term.eval t in
    let () = print_string "eval " in
    let** () = Printer.Engine.pp_term t in
    let () = print_string " := " in
    let** () = Printer.Engine.pp_term t' in
    fun ctx -> { ctx with Engine.Term.univ = Kernel.Univ.Context.empty }, (print_newline ())
  | Stop -> failwith "Stop"

