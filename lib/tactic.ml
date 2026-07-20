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
  | Revert of string (* TODO: Do an optimized version for several reverts. *)
  | Clear of string list
  | Assumption
  | Pattern of P.t list
  | Rw of P.t
  | Case of bool
  | Auto
  | Seq of t list

type error = 
  | NameConflict of string
  | NoMatchingAssumption
  | NoProgress
  | NoRw of E.t

exception Error of EC.t * error

let rec print = function
  | Exact t -> "exact " ^ (P.print t) ^ "."
  | Refine t -> "refine " ^ (P.print t) ^ "."
  | Apply l -> "apply " ^ String.concat ", " (List.map P.print l) ^ "."
  | Intro l -> "intros " ^ String.concat " " l ^ "."
  | Revert name -> "revert " ^ name ^ "."
  | Clear l -> "clear " ^ String.concat " " l ^ "."
  | Assumption -> "assumption."
  | Pattern l -> "pattern " ^ String.concat ", " (List.map P.print l) ^ "."
  | Rw t -> "rewrite " ^ P.print t ^ "."
  | Case r -> if r then "elim." else "case."
  | Auto -> "auto."
  | Seq [] -> "idtac."
  | Seq tacs -> String.concat "; " (List.map print tacs)

let print_error err =
  let ret = EC.Monad.iret in
  match err with
  | NameConflict s -> ret ("Name conflict with " ^ s ^ ".")
  | NoMatchingAssumption -> ret ("No matching assumption.")
  | NoProgress -> ret ("No progress.")
  | NoRw t -> let+* t = E.print t in "Not a rewritable relation : " ^ t ^ "."

let rec apply goal t ty ctx =
  let debug = EC.get_flag_opt "debug-synthesis" ctx in
  let () = if Option.is_some debug then let goal = E.print goal ctx in let t = E.print t ctx in let ty = E.print ty ctx in print_string (goal ^ " <- " ^ t ^ " : " ^ ty ^ "\n") else () in
  try let ctx, () = E.instantiate_evar goal t ctx in let () = if Option.is_none debug then () else print_endline ("synthesized term is " ^ E.print ~keep_evars:false t ctx) in ctx, Goal.collect_goals t ctx with | _ ->
  let ctx, (tele, ty) = E.destArity ~whd_rty:false ~until:(Exact 1) ty ctx in
  match tele with
  | [(_, argty, None, _)] ->
    let ctx, ev = EC.new_evar ~ty:(Some argty) ~with_ctx:true ctx in
    apply goal (E.mkApp [ev] t) (E.beta ev ty) ctx
  | _ -> failwith "unreachable"

let parse_hint : (string -> t) ref = ref (fun _ -> assert false)

let rec synthesize_goal goal =
  (* Do not synthesze already instantiated evars. *)
  let** t = EC.get_evar_body goal.Goal.goal in
  if Option.is_some t then EC.Monad.ret () else
  let** debug = EC.get_flag_opt "debug-synthesis" in
  let** () = if Option.is_some debug then let+* g = Goal.print goal in print_endline ("synthesize " ^ g) else EC.Monad.iret () in
  let rec try_hints = function
    | [] -> fun ctx -> raise (Error (ctx, NoProgress))
    | hint :: hints -> fun ctx -> try
    let () = if Option.is_none debug then () else print_endline ("parse hint " ^ hint) in
    let tac = !parse_hint hint in
    let ctx, subgoals = exec tac goal ctx in
    let ctx, _ = EC.Monad.List.map synthesize_goal subgoals ctx in
    ctx, ()
    with | E.TypeError _ | Error _ -> try_hints hints ctx in
  let* hints = Goal.enter goal (fun concl ->
    let* ty = E.typecheck concl in
    EC.Monad.to_mut (EC.get_hints ty)) in
  let () = if Option.is_some debug then print_endline (string_of_int (List.length hints) ^ " hints") else () in
  try_hints hints

and synthesize_term t =
  let** goals = Goal.collect_goals t in
  let+ _ = EC.Monad.List.map synthesize_goal goals in
  ()

and exec tac goal =
  let** debug = EC.get_flag_opt "debug-tac" in
  let () = if Option.is_none debug then () else print_endline ("exec " ^ print tac) in
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
    let () = if Option.is_none debug then () else print_endline ("elaborate") in
    let* t = PC.Monad.to_engine (P.elaborate t) in
    let () = if Option.is_none debug then () else print_endline ("instantiate") in
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
  | Revert name -> 
    Goal.enter goal (fun concl ->
    let** d = EC.depth in
    let* hyp = let* t = PC.Monad.to_engine (P.elaborate (P.mkConst name None)) in fun ctx -> try ctx, E.destVar t with _ -> failwith (name ^ " is not a local variable") in
    let etele, tele = List.split_at (d - 1 - hyp) goal.ctx in
    if hyp = 0 then EC.Monad.ret [{ goal with ctx = etele }] else
    let tele = List.mapi (fun i x -> (i, x)) (List.rev tele) in
    let* tele = EC.Monad.List.map (fun (i, (v, ty, t, impl)) ->
      let* ty = E.rm_problematic_term (fun t -> let+* d' = EC.depth in match t.hd with | Var j when List.is_empty t.args -> j = hyp - i + d' - d | _ -> false) ty in
      let** ty = match ty with | Some ty -> EC.Monad.iret ty | None -> fun ctx -> raise (E.TypeError (ctx, UnboundVar (hyp - i))) in
      let+ t = EC.Monad.Option.map (fun t ->
        let* t = E.rm_problematic_term (fun t -> let+* d' = EC.depth in match t.hd with | Var j when List.is_empty t.args -> j = hyp - i + d' - d | _ -> false) t in
        let** t = match t with | Some t -> EC.Monad.iret t | None -> fun ctx -> raise (E.TypeError (ctx, UnboundVar (hyp - i))) in
        EC.Monad.ret t
        ) t in
      (v, ty, t, impl)
    ) tele in
    let tele = etele @ (List.rev tele) in
    let* ty = E.typecheck concl in
    let ty = Some (E.mkForall tele (E.subst (fun i -> E.mkVar (if i = hyp then 0 else if i < hyp then i + 1 else i)) ty)) in
    let* ev = EC.new_evar ~ty ~with_ctx:false in
    let+ () = E.instantiate_evar concl (E.mkApp ((List.init (d - 1 - hyp) (fun i -> E.mkVar (d - 1 - i))) @ (List.init hyp (fun i -> E.mkVar (hyp - 1 - i))) @ [E.mkVar hyp]) ev) in
    [Goal.{ ctx = tele; goal = E.destEvar ev }])
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
    fun ctx -> { ctx with evar = IMap.add goal.goal (E.mkForall goal.ctx { ty with args = ty.args @ pats }, t, cstrs) ctx.evar }, [goal])
  | Rw rw -> Goal.enter goal (fun concl ->
    let* rw = PC.Monad.to_engine (P.elaborate rw) in
    let* rwty = E.typecheck rw in
    if List.length rwty.E.args < 2 then fun ctx -> raise (Error (ctx, NoRw rwty)) else
    let args, xy = List.split_at (List.length rwty.E.args - 2) rwty.E.args in
    let rwty = E.{ hd = rwty.hd; args } in
    let x, y = match xy with | [x; y] -> x, y | _ -> failwith "unreachable" in
    let* tyx = E.typecheck x in
    (* We extract `x` from the conclusion. *)
    let* tyg = E.typecheck concl in
    let* f = E.pattern [x] tyg in
    (* We find the proof. *)
    let* hd = E.fresh_const "RwRel" in
    let* swap_rel = E.fresh_const "swap_rel" in
    let* impl = E.fresh_const "impl" in
    let* u1 = EC.new_univ in
    let* u2 = EC.new_univ in
    let* u3 = EC.new_univ in
    let* rwrel_evar = EC.new_evar ~ty:(Some { hd = hd.hd; args = [tyx; E.mkType u1; rwty; E.mkApp [E.mkType u2; E.mkType u3; impl] swap_rel; f; x; y] }) ~with_ctx:true in
    let* () = fun ctx -> try synthesize_goal Goal.{ ctx = (List.map snd (IMap.to_list ctx.E.var)); goal = E.destEvar (E.of_hd rwrel_evar.hd) } ctx with E.TypeError _ -> raise (Error (ctx, NoRw rwty)) in
    let fy = E.{ hd = f.hd; args = [y] } in
    let** fy = E.whd ~flags:{ E.whd_flags_none with beta = true; steps = Some 1 } fy in
    let* ry = EC.new_evar ~ty:(Some fy) ~with_ctx:true in
    let* () = E.instantiate_evar concl (E.mkApp [rw; ry] rwrel_evar) in
    let** subgoals = Goal.collect_goals ry in
    EC.Monad.ret subgoals)
  | Case r -> Goal.enter goal (fun concl ->
    let* gty = E.typecheck concl in
    let* tele, _ = E.destArity ~whd_rty:false ~keep_let:true ~until:(Exact 1) ~count_implicits:true gty in
    match tele with | [] | _ :: _ :: _ -> failwith "unreachable" | [(_, ind, _, _)] ->
    let** (_, a, c) = let+* ind = E.whd ind in E.destInd (E.of_hd ind.hd) in
    let* atele, _ = E.destArity ~whd_rty:false ~keep_let:false ~count_implicits:true a in
    let n = List.length atele in
    let args, indargs = List.split_at (List.length ind.args - n) ind.args in
    let indhd = { ind with args } in
    let* gty = E.pattern indargs gty in
    let tele, gty = if n = 0 then [], gty else
      match gty.hd with | Fun (f, tele, body) -> let tele, rtele = List.split_at n tele in tele, E.mkForallOrFun f rtele body | _ -> failwith "unreachable" in
    let** () = if Option.is_none debug then EC.Monad.iret () else
      let+* gty = E.print gty in
      print_endline ("gty = " ^ gty) in
    let* tele1, gty = EC.with_telescope ~avoid_capture:false tele (E.destArity ~whd_rty:false ~keep_let:true ~until:(Exact 1) ~count_implicits:true gty) in
    let tele = tele @ [List.hd tele1] in
    let t = E.mkApp [E.mkFun tele gty] (E.mkCase indhd r) in
    let** () = if Option.is_none debug then EC.Monad.iret () else
      let+* t = E.print t in
      print_endline ("t = " ^ t) in
    let* ty = E.typecheck t in
    let** () = if Option.is_none debug then EC.Monad.iret () else
      let+* ty = E.print ~debug:true ty in
      print_endline ("ty = " ^ ty) in
    let* ctele, _ = E.destArity ~until:(Exact (List.length c)) ty in
    let* c = EC.Monad.List.map (fun (i, (_, ty, _, _)) -> EC.new_evar ~ty:(Some (E.bump (- i) ty)) ~with_ctx:true) (List.mapi (fun i x -> (i, x)) ctele) in
    let* () = E.instantiate_evar concl (E.mkApp (c @ indargs) t) in
    let** subgoals = Goal.collect_goals concl in
    ret subgoals)
  | Auto -> let+ _ = synthesize_goal goal in []
  | Seq [] -> ret [goal]
  | Seq (tac :: tacs) ->
(*     let () = print_endline ("seq") in *)
    let* subgoals = exec tac goal in
    let+ subgoals = EC.Monad.List.map (fun g -> let** t = EC.get_evar_body (g.Goal.goal) in if t = None then exec (Seq tacs) g else ret []) subgoals in
    List.concat subgoals

let _ = E.synthesize := synthesize_term
