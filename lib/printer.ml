open Utils

let rec pp_term ctx t =
  let ( ++ ) = fun _ s -> print_string s in
  let rec pr_telescope ?(notype=false) ctx = function
    | [] -> ctx
    | (v, t) :: args ->
      let ctx' = Term.Context.push_var (Some v, t, None) ctx in
      let () = if notype then () ++ " " ++ v else () ++ " (" ++ v ++ " : "; pp_term ctx t ++ ")" in
      pr_telescope ~notype ctx' args in
  let atomic = function
    | Term.Var _ | Term.Const _ | Term.Type _ | Term.Case (_, _) | Term.Construct (_, _) -> true
    | _ -> false in
  match t with
  | Term.Fun (tele, body) -> () ++ "fun";
      let ctx = pr_telescope ctx tele in
      () ++ ", "; pp_term ctx body
  | Term.Pi (tele, body) -> () ++ "forall";
      let ctx = pr_telescope ctx tele in
      () ++ ", "; pp_term ctx body
  | Term.Let (v, ty, t, body) -> () ++ "let " ++ v ++ " : "; pp_term ctx ty ++ " := "; pp_term ctx t ++ " in "; pp_term (Term.Context.push_var (Some v, t, None) ctx) body
  | Term.Var v -> () ++ Term.Context.get_var_name ctx v
  | Term.Const v -> () ++ v
  | Term.App (f :: a) ->
    let (+) = fun _ e -> if atomic e then pp_term ctx e else (() ++ "("; pp_term ctx e ++ ")") in
    () + f; List.iter (fun e -> () ++ " " + e) a
  | Term.Type l -> let pr_atom v i =
      if v = "" then
        (if i = 0 then
          () ++ "Prop"
        else (() ++ "Type@{"; print_int i ++ "}"))
      else if i = 0 then () ++ v else (() ++ v ++ "+"; print_int i) in
    if SMap.cardinal l = 1 then
      let (v, i) = SMap.choose l in pr_atom v i
    else (() ++ "Type@{max("; SMap.iter (fun v i -> pr_atom v i ++ ", ") l ++ ")")
  | Ind (arity, constructors) ->
    () ++ "ind";
    (* Dummy type, just for having something in the context. *)
    let ctx = Term.Context.push_var (None, arity, None) ctx in
    () ++ " : "; pp_term ctx arity ++ " :="; List.iter (fun t -> () ++ " | "; pp_term ctx t) constructors
  | Construct (ind, id) ->
    (if atomic ind then pp_term ctx ind else (() ++ "("; pp_term ctx ind ++ ")")) ++ ".mk"; print_int id
  | Case (ind, recursive) ->
    (if atomic ind then pp_term ctx ind else (() ++ "("; pp_term ctx ind ++ ")")) ++ (if recursive then ".fix" else ".case")
  | _ -> raise (Term.TypeError (Term.Context.empty, Term.IllFormed t))

let pp_ctx ctx =
  print_string "CTX:\n\t Local variables:\n";
  List.iteri (fun i (v, ty, t) -> print_string "\t\t"; print_string (Option.value v ~default:("_" ^ string_of_int i)); print_string " : "; pp_term ctx ty; (match t with | None -> () | Some t -> print_string " := "; pp_term ctx t); print_string "\n") ctx.var;
  print_string "\n\t Global variables:\n";
  SMap.iter (fun v (ty, body) -> print_string "\t\t"; print_string v; print_string " : "; pp_term ctx ty; print_string " := "; pp_term ctx body; print_string "\n") ctx.const;
  print_string "\n"

let print_type_error ?(debug=false) ctx e =
  let print = if debug then Term.print else pp_term ctx in
  match e with
  | Term.UnboundVar i -> print_string "Unbound variable "; print_int i; print_string "\n"
  | Term.UnboundConst v -> print_string "Unbound constant "; print_string v; print_string "\n"
  | Term.NotAType t -> print t; print_string " has type "; print (Term.type_of ctx t); print_string ", it is not a type\n"
  | Term.IllegalApplication t -> print_string "Illegal application in "; print t; print_string "\n"
  | Term.TypeMismatch (ty, t) ->
    let tyt = try Term.type_of ctx t with e -> if debug then Const "???" else raise e in
    print_string "Term "; print t; print_string " has type "; print tyt; print_string " while it is expected to have type "; print ty; print_string "\n"
  | Term.IllFormed t -> print t; print_string " is ill-formed\n"
  | Term.NoBody t -> print t; print_string "has no body\n"
  | Term.NotGround t -> print t; print_string "is not ground\n"
  | Term.IllegalConstructorReturnType t -> print_string "Constructor should return an element of the inductive type, but has type "; print t; print_string "\n"
  | Term.NonPositive t -> print_string "Constructor of type "; print t; print_string " is not positive\n"
  | Term.PropElimination t -> print_string "Cannot eliminate "; print t; print_string "outside of Prop\n"
