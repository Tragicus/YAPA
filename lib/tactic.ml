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
  | Pattern of P.t list
  | Auto
  | Seq of t list

type error = 
  | NameConflict of string
  | NoMatchingAssumption
  | NoProgress

exception Error of EC.t * error

let rec print = function
  | Exact t -> "exact " ^ (P.print t) ^ "."
  | Refine t -> "refine " ^ (P.print t) ^ "."
  | Apply l -> "apply " ^ String.concat ", " (List.map P.print l) ^ "."
  | Intro l -> "intros " ^ String.concat " " l ^ "."
  | Clear l -> "clear " ^ String.concat " " l ^ "."
  | Assumption -> "assumption."
  | Pattern l -> "pattern " ^ String.concat ", " (List.map P.print l) ^ "."
  | Auto -> "auto."
  | Seq [] -> "idtac."
  | Seq tacs -> String.concat "; " (List.map print tacs)

let print_error = function
  | NameConflict s -> "Name conflict with " ^ s
  | NoMatchingAssumption -> "No matching assumption"
  | NoProgress -> "No progress"

let rec apply goal t ty ctx =
(*   let () = let goal = E.print goal ctx in let t = E.print t ctx in let ty = E.print ty ctx in print_string (goal ^ " <- " ^ t ^ " : " ^ ty ^ "\n") in *)
  try let ctx, () = E.instantiate_evar goal t ctx in ctx, Goal.collect_goals t ctx with | _ ->
  let ctx, (tele, ty) = E.destArity ~whd_rty:false ~until:(Exact 1) ty ctx in
  match tele with
  | [(_, argty, None, _)] ->
    let ctx, ev = EC.new_evar ~ty:(Some argty) ~with_ctx:true ctx in
    apply goal (E.mkApp [ev] t) (E.beta ev ty) ctx
  | _ -> failwith "unreachable"

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
(*     let** () = let** tg = E.print tg in let+* t = E.print t in print_endline ("apply " ^ t ^ " : " ^ tg) in *)
    let* ty = E.typecheck t in
    apply goal t ty)
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
  | Pattern pats -> Goal.enter goal (fun g ->
    let* pats = EC.Monad.List.map (fun t -> PC.Monad.to_engine (P.elaborate t)) pats in
    let* ty = E.typecheck g in
    let* ty = E.pattern pats ty in
    let** (_, t, cstrs) = EC.find_evar goal.goal in
    fun ctx -> { ctx with evar = IMap.add goal.goal (E.mkForall goal.ctx ty, t, cstrs) ctx.evar }, [goal])
  | Auto -> Goal.enter goal (fun concl ->
    let* tg = E.typecheck concl in
    let rec try_hints = function
      | [] -> fun ctx -> raise (Error (ctx, NoProgress))
      | hint :: hints ->
(*       let** () = let+* hint = E.print hint in print_string ("try hint " ^ hint ^ "\n") in *)
      let* ty = E.typecheck hint in fun ctx ->
      try apply concl hint ty ctx with | _ ->
      try_hints hints ctx in
    let** hints = EC.get_hints tg in
    try_hints hints)
  | Seq [] -> ret [goal]
  | Seq (tac :: tacs) ->
(*     let () = print_endline ("seq") in *)
    let* subgoals = exec tac goal in
    let+ subgoals = EC.Monad.List.map (fun g -> let** t = EC.get_evar_body (g.Goal.goal) in if t = None then exec (Seq tacs) g else ret []) subgoals in
    List.concat subgoals










    





  
