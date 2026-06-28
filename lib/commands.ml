open Utils
module E = Engine.Term
module EC = E.Context
module P = Term
module PC = P.Context

type t =
  | Print of P.t
  | Check of P.t
  | Whd of P.t
  | Eval of P.t
  | Define of string * (string list * string list) option * P.t * P.t
  | Tac of Tactic.t
  | Qed of bool
  | Hint of P.t (* pat *) * P.t (* hint *)
  | Skip
  | Set of string (* flag *) * string (* value *)
  | Unset of string (* flag *)
  | Stop

type error =
  | NoGoal
  | OpenGoals
  | Stop

type status = | Idle | Proofmode of string * E.t * E.t * Goal.t list
type context = EC.t * status

exception Error of context * error

module Context = struct
  type t = context

  let empty = (EC.empty, Idle)

  let enter_goal0 f ctx = match ctx with
    | _, Idle | _, Proofmode (_, _, _, []) -> raise (Error (ctx, NoGoal))
    | ectx, Proofmode (_, _, _, g :: _) -> Goal.enter g f ectx

  let goal_count ctx = match snd ctx with
    | Idle -> 0
    | Proofmode (_, _, _, gs) -> List.length gs

  module Monad = struct
    include Utils.ContextMonad(struct type t = context end)

    let of_engine f (ctx, status) =
      let ctx, r = f ctx in
      (ctx, status), r
  end
end

open Context.Monad.Notations

let print cmd =
  let (+) = String.cat in
  match cmd with
  | Print t -> "Print " + Term.print t
  | Check t -> "Check " + Term.print t
  | Whd t -> "Whd " + Term.print t
  | Eval t -> "Eval " + Term.print t
  | Define (c, su, ty, t) -> "Definition " + Term.print (Term.mkConst c (Option.map (fun (s, u) -> s, List.map (fun u -> SMap.singleton u 0) u) su)) + " : " + Term.print ty + " := " + Term.print t
  | Tac tac -> Tactic.print tac
  | Qed b -> if b then "Defined" else "Qed"
  | Hint (pat, hint) -> "Hint " + Term.print hint + " for " + Term.print pat
  | Skip -> "Skip"
  | Set (flag, value) -> "Set " + flag + " := " + value
  | Unset flag -> "Unset " + flag
  | Stop -> "Stop"

let eval cmd : unit Context.Monad.t =
  let (+) = String.cat in
  let ret = Context.Monad.ret in
  let () = print_endline (print cmd) in
  match cmd with
  | Print t ->
    let (c, _) = try P.destConst t with _ -> failwith "I can only print the body of constants" in
    let* (univ, _, body) = Context.Monad.of_engine (EC.Monad.to_mut (EC.find_const c)) in
    (match body with
    | None -> fun (ctx, _) -> raise (E.TypeError (ctx, E.NoBody (E.mkConst c [] [])))
    | Some t ->
    let+ t = Context.Monad.of_engine (EC.Monad.to_mut (E.print (E.of_kernel t))) in
    print_endline (c + "@{" + String.concat ", " (List.init (IMap.cardinal univ.sorts) (fun i -> "s_" + string_of_int i)) + "; " + String.concat ", " (List.init (IMap.cardinal univ.levels - 1) (fun i -> "u_" + string_of_int Int.(i + 1))) + "} := " + t))
  | Check t ->
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* ty = Context.Monad.of_engine (E.typecheck t) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print ~keep_evars:false t)) in
    let+ ty = Context.Monad.of_engine (EC.Monad.to_mut (E.print ~keep_evars:false ty)) in
    print_endline (t + " : " + ty)
  | Define (v, su, ty, t) ->
    let** () = fun ctx -> let () = assert (IMap.cardinal (fst ctx).E.var = 0) in match snd ctx with | Idle -> () | Proofmode (_, _, _, _) -> raise (Error (ctx, OpenGoals)) in
    let (s, u) = Option.value ~default:([], []) su in
    let* sort = Context.Monad.of_engine (EC.Monad.List.fold_left (fun vs ss ctx -> let ctx, s = EC.new_sort (Some vs) ctx in ctx, SMap.add vs s ss) s SMap.empty) in
    let* univ = Context.Monad.of_engine (EC.Monad.List.fold_left (fun vu us ctx -> let ctx, u = EC.new_level (Some vu) ctx in ctx, SMap.add vu u us) u SMap.empty) in
    let** pctx = fun (ctx, _) -> P.Context.{ var = SMap.empty; sort; univ; evar = SMap.empty; ctx } in
    let pctx, ty = P.elaborate ty pctx in
    let pctx, t = P.elaborate t pctx in
    let* () = fun (_, status) -> (pctx.ctx, status), () in
    let* tyb = Context.Monad.of_engine (E.typecheck t) in
    let* b = Context.Monad.of_engine (E.unify tyb ty) in
    if not b then fun (ctx, _) -> raise (E.TypeError (ctx, E.TypeMismatch (ty, t))) else
    let* gs = Context.Monad.of_engine (EC.Monad.to_mut (Goal.collect_goals t)) in
    fun (ctx, _) -> (if gs = [] then (let ctx, () = EC.push_const v (ty, Some t) ctx in EC.reset ctx), Idle else (ctx, Proofmode (v, ty, t, gs))), ()
  | Tac tac ->
    let* goal = fun (ctx, status) ->
      let status, g = match status with | Proofmode (v, ty, t, g :: gs) -> Proofmode (v, ty, t, gs), g | _ -> raise (Error ((ctx, status), NoGoal)) in
      (ctx, status), g in
    let* subgoals = Context.Monad.of_engine (Tactic.exec tac goal) in
    fun (ctx, status) ->
      let status = match status with | Idle -> failwith "unreachable" | Proofmode (v, ty, t, gs) ->
        let gs = List.filter (fun g -> let t = EC.get_evar_body g.Goal.goal ctx in t = None) (subgoals @ gs) in
        Proofmode (v, ty, t, gs) in
      (ctx, status), ()
  | Qed transparent -> fun (ctx, status) -> 
    (match status with | Idle -> raise (Error ((ctx, status), NoGoal)) | Proofmode (_, _, _, _ :: _) -> raise (Error ((ctx, status), OpenGoals)) | Proofmode (v, ty, t, []) ->
    let ctx, () = EC.push_const v (ty, if transparent then Some t else None) ctx in
    (EC.reset ctx, Idle), ())
  | Hint (pat, hint) ->
    let* pat = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate pat)) in
    let* pat = Context.Monad.of_engine (EC.Monad.to_mut (E.to_pattern pat)) in 
    let* hint = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate hint)) in
    let* hint = Context.Monad.of_engine (EC.Monad.to_mut (E.to_kernel hint)) in
    fun (ctx, status) -> ({ ctx with hints = Engine.Pattern.Map.add pat hint ctx.hints }, status), ()
  | Whd t ->
    let** ctx = fun (ctx, _) -> ctx in
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.whd t)) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.print t')) in
    let () = print_endline ("whd " + t + " := " + t') in
    (* Do not forget to restore the context. *)
    fun (_, status) -> (ctx, status), ()
  | Eval t ->
    let** ctx = fun (ctx, _) -> ctx in
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.eval t)) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.print t')) in
    let () = print_endline ("eval " + t + " := " + t') in
    (* Do not forget to restore the context. *)
    fun (_, status) -> (ctx, status), ()
  | Skip -> ret ()
  | Set (flag, value) -> fun (ctx, status) ->
    let ctx, () = EC.add_flag flag value ctx in
    (ctx, status), ()
  | Unset flag -> fun (ctx, status) ->
    let ctx, () = EC.remove_flag flag ctx in
    (ctx, status), ()
  | Stop -> fun (ctx, status) ->
    let () = match status with
      | Proofmode (_, _, _, g :: _) -> print_endline (Goal.print g ctx)
      | _ -> () in
    let () = print_endline (EC.print ctx) in
    raise (Error ((ctx, status), Stop))

let print_error e _ctx =
  match e with
  | Stop -> "Stop"
  | NoGoal -> "No open goal"
  | OpenGoals -> "Open goal(s) remaining"
