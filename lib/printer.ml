open Utils
open Kernel.Term.Context.Monad.Notations

let rec pp_term t ctx =
  let ( ++ ) = fun _ s -> print_string s in
  let pr_telescope ?(notype=false) tele k =
    Kernel.Term.Context.Monad.to_imut (Kernel.Term.Context.Monad.fold_telescope
      (fun _ (v, t) ->
        if notype then Kernel.Term.Context.Monad.ret (() ++ " " ++ v) else
        let () = () ++ " (" ++ v ++ " : " in
        let** () = pp_term t in
        Kernel.Term.Context.Monad.ret (() ++ ")"))
      () tele
      (fun _ -> Kernel.Term.Context.Monad.to_mut (k ()))) in
  let atomic = function
    | Kernel.Term.Var _ | Kernel.Term.Const _ | Kernel.Term.Type _ | Kernel.Term.Case (_, _) | Kernel.Term.Construct (_, _) -> true
    | _ -> false in
  match t with
  | Kernel.Term.Fun (tele, body) -> () ++ "fun";
    pr_telescope tele (fun _ -> () ++ ", "; pp_term body) ctx
  | Kernel.Term.Pi (tele, body) -> () ++ "forall";
    pr_telescope tele (fun _ -> () ++ ", "; pp_term body) ctx
  | Kernel.Term.Let (v, ty, t, body) -> () ++ "let " ++ v ++ " : "; pp_term ty ctx ++ " := "; pp_term t ctx ++ " in ";
    Kernel.Term.Context.Monad.to_imut (Kernel.Term.Context.Monad.with_var (Some v, t, None) (Kernel.Term.Context.Monad.to_mut (pp_term body))) ctx
  | Kernel.Term.Var v -> () ++ Kernel.Term.Context.get_var_name v ctx
  | Kernel.Term.Const (us, v) -> () ++ v ++ "@{"; Utils.print_with_sep ", " Kernel.Univ.print us ++ "}"
  | Kernel.Term.App (f :: a) ->
    let (+) = fun _ e -> if atomic e then pp_term e ctx else (() ++ "("; pp_term e ctx ++ ")") in
    () + f; List.iter (fun e -> () ++ " " + e) a
  | Kernel.Term.Type u ->
    if Kernel.Univ.isProp u then () ++ "Prop" else
    () ++ "Type@{"; Kernel.Univ.print u ++ "}"
  | Ind (arity, constructors) ->
    () ++ "ind" ++ " : "; pp_term arity ctx ++ " :=";
    Kernel.Term.Context.Monad.to_imut (Kernel.Term.Context.Monad.with_var (None, arity, None) (Kernel.Term.Context.Monad.to_mut (fun ctx ->
      List.iter (fun t -> () ++ " | "; pp_term t ctx) constructors))) ctx
  | Construct (ind, id) ->
    (if atomic ind then pp_term ind ctx else (() ++ "("; pp_term ind ctx ++ ")")) ++ ".mk"; print_int id
  | Case (ind, recursive) ->
    (if atomic ind then pp_term ind ctx else (() ++ "("; pp_term ind ctx ++ ")")) ++ (if recursive then ".fix" else ".case")
  | _ -> raise (Kernel.Term.TypeError (Kernel.Term.Context.empty, Kernel.Term.IllFormed t))

let pp_ctx ctx =
  print_string "CTX:\n\t Local variables:\n";
  List.iteri (fun i (v, ty, t) -> print_string "\t\t"; print_string (Option.value v ~default:("_" ^ string_of_int i)); print_string " : "; pp_term ty ctx; (match t with | None -> () | Some t -> print_string " := "; pp_term t ctx); print_string "\n") ctx.var;
  print_string "\n\t Global variables:\n";
  SMap.iter (fun v (_, ty, body) -> print_string "\t\t"; print_string v; print_string " : "; pp_term ty ctx; print_string " := "; pp_term body ctx; print_string "\n") ctx.const;
  print_string "\n"

let print_type_error ?(debug=false) e ctx =
  let print t = if debug then Kernel.Term.print t else pp_term t ctx in
  match e with
  | Kernel.Term.UnboundVar i -> print_string "Unbound variable "; print_int i; print_string "\n"
  | Kernel.Term.UnboundConst v -> print_string "Unbound constant "; print_string v; print_string "\n"
  | Kernel.Term.NotAType t -> print t; print_string " has type "; print (Kernel.Term.Context.Monad.to_imut (Kernel.Term.type_of t) ctx); print_string ", it is not a type\n"
  | Kernel.Term.IllegalApplication t -> print_string "Illegal application in "; print t; print_string "\n"
  | Kernel.Term.TypeMismatch (ty, t) ->
    let tyt = try Kernel.Term.Context.Monad.to_imut (Kernel.Term.type_of t) ctx with e -> if debug then Kernel.Term.Const ([], "???") else raise e in
    print_string "Kernel.Term "; print t; print_string " has type "; print tyt; print_string " while it is expected to have type "; print ty; print_string "\n"
  | Kernel.Term.IllFormed t -> print t; print_string " is ill-formed\n"
  | Kernel.Term.NoBody t -> print t; print_string "has no body\n"
  | Kernel.Term.NotGround t -> print t; print_string "is not ground\n"
  | Kernel.Term.IllegalConstructorReturnType t -> print_string "Constructor should return an element of the inductive type, but has type "; print t; print_string "\n"
  | Kernel.Term.NonPositive t -> print_string "Constructor of type "; print t; print_string " is not positive\n"
  | Kernel.Term.PropElimination t -> print_string "Cannot eliminate "; print t; print_string "outside of Prop\n"
