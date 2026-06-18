open Utils
module P = Term
module PC = P.Context
module E = Engine.Term
module EC = E.Context
open EC.Monad.Notations

type t =
  | Exact of P.t
  | Refine of P.t
  | Apply of P.t list
  | Intro of string list
  | Clear of string list
  | Assumption
  | Seq of t list

type error = 
  | NameConflict of string
  | NoMatchingAssumption

exception Error of EC.t * error

let rec print = function
  | Exact t -> "exact " ^ (P.print t) ^ "."
  | Refine t -> "refine " ^ (P.print t) ^ "."
  | Apply l -> "apply " ^ String.concat ", " (List.map P.print l) ^ "."
  | Intro l -> "intros " ^ String.concat " " l ^ "."
  | Clear l -> "clear " ^ String.concat " " l ^ "."
  | Assumption -> "assumption."
  | Seq [] -> "idtac."
  | Seq tacs -> String.concat "; " (List.map print tacs)

let rec exec tac goal =
(*   let () = print_endline ("exec " ^ print tac) in *)
  let ret = EC.Monad.ret in
  match tac with
  | Exact t ->
    let* subgoals = exec (Refine t) goal in
    (match subgoals with
    | [] -> ret []
    | _ ->  
      let* t = PC.Monad.to_engine (P.elaborate t) in
      fun ctx -> raise E.(TypeError (ctx, NotGround t)))
  | Refine t ->
    Goal.enter goal (fun goal ->
    let* t = PC.Monad.to_engine (P.elaborate t) in
    let* () = E.instantiate_evar goal t in
    let** subgoals = Goal.collect_goals t in
    ret subgoals)
  | Apply [] ->
      let** v = fun ctx -> Utils.fresh_name "_" (List.map (fun (_, (v, _, _, _)) -> v) (IMap.to_list ctx.E.var)) in
      exec (Seq [Intro [v]; Apply [P.mkVar v]; Clear [v]]) goal
  | Apply [t] ->
    Goal.enter goal (fun goal ->
    let* t = PC.Monad.to_engine (P.elaborate t) in
    let* tg = E.typecheck goal in
(*     let** () = let** tg = E.print tg in let+* t = E.print t in print_endline ("apply " ^ t ^ " : " ^ tg) in *)
    let rec apply t ty =
      let* b = E.unify ~cumulative:E.Cumul ty tg in
      if b then let* () = E.instantiate_evar goal t in EC.Monad.to_mut (Goal.collect_goals t) else
      let* tele, ty = E.destArity ~whd_rty:false ~until:(Exact 1) ty in
      match tele with
      | [(_, argty, None, _)] ->
        let* ev = EC.new_evar ~ty:(Some argty) ~with_ctx:true in
        apply (E.mkApp [ev] t) (E.beta ev ty)
      | _ -> failwith "unreachable" in
    let* ty = E.typecheck t in
    apply t ty)
  | Apply l -> exec (Seq (List.map (fun t -> Apply [t]) l)) goal
  | Intro names -> 
    let** _ = fun ctx ->
      let vars = SSet.of_list (List.map (fun (_, (v, _, _, _)) -> v) (IMap.to_list ctx.E.var)) in
      List.fold_left (fun vars v ->
        if SSet.mem v vars then raise (Error (ctx, NameConflict v)) else
        SSet.add v vars
      ) vars names in
    Goal.enter goal (fun t ->
    let* ty = E.typecheck t in
    let* tele, _ = E.destArity ~whd_rty:false ~keep_let:true ~until:(Exact (List.length names)) ty in
    let tele = List.map (fun (v, (_, ty, t, impl)) -> (v, ty, t, impl)) (List.combine names tele) in
    ret [{ goal with ctx = goal.ctx @ tele }])
  | Clear [] -> ret [goal]
  | Clear hyps ->
    Goal.enter goal (fun concl ->
    let** d = EC.depth in
    let* hyps = EC.Monad.List.map (fun hyp -> let* t = PC.Monad.to_engine (P.elaborate (P.mkConst hyp None)) in fun ctx -> try ctx, d - 1 - E.destVar t with _ -> failwith (hyp ^ " is not a local variable")) hyps in
    let hyps = ISet.of_list hyps in
    let* ev = E.prune_evar hyps (E.destEvar (E.of_hd concl.E.hd)) in
    let* ty = E.typecheck ev in
    let* tele, _ = E.destArity ~until:(Exact (d - ISet.cardinal hyps)) ty in
    let g = Goal.{ ctx = tele; goal = E.destEvar ev } in
    ret [g])
  | Assumption -> Goal.enter goal (fun concl ->
(*     let** () = let+* concl = E.print concl in print_endline ("assumption " ^ concl) in *)
    let** d = EC.depth in
    let rec loop i ctx =
      if i = d then raise (Error (ctx, NoMatchingAssumption)) else
      try let ctx, () = E.instantiate_evar concl (E.mkVar i) ctx in ctx, []
      with _ -> loop (i + 1) ctx in
    loop 0)
  | Seq [] -> ret [goal]
  | Seq (tac :: tacs) ->
(*     let () = print_endline ("seq") in *)
    let* subgoals = exec tac goal in
    let+ subgoals = EC.Monad.List.map (fun g -> let** t = EC.get_evar_body (g.Goal.goal) in if t = None then exec (Seq tacs) g else ret []) subgoals in
    List.concat subgoals










    





  
