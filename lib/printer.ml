open Utils
open Term.Context.Monad.Notations

let rec pp_term t ctx =
  let ( ++ ) = fun _ s -> print_string s in
  let pr_telescope ?(notype=false) tele k =
    Term.Context.Monad.to_imut (Term.Context.Monad.fold_telescope
      (fun _ (v, t) ->
        if notype then Term.Context.Monad.ret (() ++ " " ++ v) else
        let () = () ++ " (" ++ v ++ " : " in
        let** () = pp_term t in
        Term.Context.Monad.ret (() ++ ")"))
      () tele
      (fun _ -> Term.Context.Monad.to_mut (k ()))) in
  let atomic = function
    | Term.Var _ | Term.Const _ | Term.Type _ | Term.Case (_, _) | Term.Construct (_, _) -> true
    | _ -> false in
  match t with
  | Term.Fun (tele, body) -> () ++ "fun";
    pr_telescope tele (fun _ -> () ++ ", "; pp_term body) ctx
  | Term.Pi (tele, body) -> () ++ "forall";
    pr_telescope tele (fun _ -> () ++ ", "; pp_term body) ctx
  | Term.Let (v, ty, t, body) -> () ++ "let " ++ v ++ " : "; pp_term ty ctx ++ " := "; pp_term t ctx ++ " in ";
    Term.Context.Monad.to_imut (Term.Context.Monad.with_var (Some v, t, None) (Term.Context.Monad.to_mut (pp_term body))) ctx
  | Term.Var v -> () ++ Term.Context.get_var_name v ctx
  | Term.Const v -> () ++ v
  | Term.App (f :: a) ->
    let (+) = fun _ e -> if atomic e then pp_term e ctx else (() ++ "("; pp_term e ctx ++ ")") in
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
    () ++ "ind" ++ " : "; pp_term arity ctx ++ " :=";
    Term.Context.Monad.to_imut (Term.Context.Monad.with_var (None, arity, None) (Term.Context.Monad.to_mut (fun ctx ->
      List.iter (fun t -> () ++ " | "; pp_term t ctx) constructors))) ctx
  | Construct (ind, id) ->
    (if atomic ind then pp_term ind ctx else (() ++ "("; pp_term ind ctx ++ ")")) ++ ".mk"; print_int id
  | Case (ind, recursive) ->
    (if atomic ind then pp_term ind ctx else (() ++ "("; pp_term ind ctx ++ ")")) ++ (if recursive then ".fix" else ".case")
  | _ -> raise (Term.TypeError (Term.Context.empty, Term.IllFormed t))

let pp_ctx ctx =
  print_string "CTX:\n\t Local variables:\n";
  List.iteri (fun i (v, ty, t) -> print_string "\t\t"; print_string (Option.value v ~default:("_" ^ string_of_int i)); print_string " : "; pp_term ty ctx; (match t with | None -> () | Some t -> print_string " := "; pp_term t ctx); print_string "\n") ctx.var;
  print_string "\n\t Global variables:\n";
  SMap.iter (fun v (ty, body) -> print_string "\t\t"; print_string v; print_string " : "; pp_term ty ctx; print_string " := "; pp_term body ctx; print_string "\n") ctx.const;
  print_string "\n"

let print_type_error ?(debug=false) e ctx =
  let print t = if debug then Term.print t else pp_term t ctx in
  match e with
  | Term.UnboundVar i -> print_string "Unbound variable "; print_int i; print_string "\n"
  | Term.UnboundConst v -> print_string "Unbound constant "; print_string v; print_string "\n"
  | Term.NotAType t -> print t; print_string " has type "; print (Term.Context.Monad.to_imut (Term.type_of t) ctx); print_string ", it is not a type\n"
  | Term.IllegalApplication t -> print_string "Illegal application in "; print t; print_string "\n"
  | Term.TypeMismatch (ty, t) ->
    let tyt = try Term.Context.Monad.to_imut (Term.type_of t) ctx with e -> if debug then Term.Const "???" else raise e in
    print_string "Term "; print t; print_string " has type "; print tyt; print_string " while it is expected to have type "; print ty; print_string "\n"
  | Term.IllFormed t -> print t; print_string " is ill-formed\n"
  | Term.NoBody t -> print t; print_string "has no body\n"
  | Term.NotGround t -> print t; print_string "is not ground\n"
  | Term.IllegalConstructorReturnType t -> print_string "Constructor should return an element of the inductive type, but has type "; print t; print_string "\n"
  | Term.NonPositive t -> print_string "Constructor of type "; print t; print_string " is not positive\n"
  | Term.PropElimination t -> print_string "Cannot eliminate "; print t; print_string "outside of Prop\n"
