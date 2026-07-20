open Utils
module K = Kernel.Term
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
  | Hint of P.t (* pat *) * string (* hint *)
  | Skip
  | Import of string
  | Set of string (* flag *) * string (* value *)
  | Unset of string (* flag *)
  | Stop

type error =
  | NoGoal
  | OpenGoals
  | Stop
  | AlreadyDefined of string

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

module Serialized = struct
  type t =
    | Define of string * Kernel.Univ.Context.t * K.t * K.t option
    | Hint of Engine.Pattern.t * string
  [@@deriving sexp]
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
  | Hint (pat, hint) -> "Hint " + hint + " for " + Term.print pat
  | Skip -> "Skip"
  | Import s -> "Import " + s
  | Set (flag, value) -> "Set " + flag + " := " + value
  | Unset flag -> "Unset " + flag
  | Stop -> "Stop"

let eval cmd : Serialized.t option Context.Monad.t =
  let (+) = String.cat in
  let ret = Context.Monad.ret in
(*   let () = print_endline (print cmd) in *)
  match cmd with
  | Print t ->
    let (c, _) = try P.destConst t with _ -> failwith "I can only print the body of constants" in
    let* (univ, _, body) = Context.Monad.of_engine (EC.Monad.to_mut (EC.find_const c)) in
    (match body with
    | None -> fun (ctx, _) -> raise (E.TypeError (ctx, E.NoBody (E.mkConst c [] [])))
    | Some t ->
    let+ t = Context.Monad.of_engine (EC.Monad.to_mut (E.print (E.of_kernel t))) in
    let () = print_endline (c + "@{" + String.concat ", " (List.init (IMap.cardinal univ.sorts) (fun i -> "s_" + string_of_int i)) + "; " + String.concat ", " (List.init (IMap.cardinal univ.levels - 1) (fun i -> "u_" + string_of_int Int.(i + 1))) + "} := " + t) in
    None)
  | Check t ->
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* ty = Context.Monad.of_engine (E.typecheck t) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print ~keep_evars:false t)) in
    let+ ty = Context.Monad.of_engine (EC.Monad.to_mut (E.print ~keep_evars:false ty)) in
    let () = print_endline (t + " : " + ty) in
    None
  | Define (v, su, ty, t) ->
    let** () = fun (ctx, status) ->
      let () = assert (IMap.cardinal ctx.E.var = 0) in
      let x = try Some (EC.find_const v ctx) with _ -> None in
      if Option.is_some x then raise (Error ((ctx, status), AlreadyDefined v)) else
      match status with | Idle -> () | Proofmode (_, _, _, _) -> raise (Error ((ctx, status), OpenGoals)) in
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
    let* () = fun (ctx, _) -> (if gs = [] then (let ctx, () = EC.push_const v (ty, Some t) ctx in EC.reset ctx), Idle else (ctx, Proofmode (v, ty, t, gs))), () in
    let** r = fun (ctx, _) -> 
      try let u, ty, t = EC.find_const v ctx in Some (Serialized.Define (v, u, ty, t)) with _ -> None in
    Context.Monad.ret r
  | Tac tac ->
    let* goal = fun (ctx, status) ->
      let status, g = match status with | Proofmode (v, ty, t, g :: gs) -> Proofmode (v, ty, t, gs), g | _ -> raise (Error ((ctx, status), NoGoal)) in
      (ctx, status), g in
    let* subgoals = Context.Monad.of_engine (Tactic.exec tac goal) in
    let** debug = fun (ctx, _) -> EC.get_flag_opt "debug-tactic" ctx in
    let () = if Option.is_none debug then () else print_endline (string_of_int (List.length subgoals) ^ " subgoals") in
    fun (ctx, status) ->
      let status = match status with | Idle -> failwith "unreachable" | Proofmode (v, ty, t, gs) ->
        let gs = List.filter (fun g -> let t = EC.get_evar_body g.Goal.goal ctx in t = None) (subgoals @ gs) in
        Proofmode (v, ty, t, gs) in
      (ctx, status), None
  | Qed transparent -> fun (ctx, status) -> 
    (match status with | Idle -> raise (Error ((ctx, status), NoGoal)) | Proofmode (_, _, _, _ :: _) -> raise (Error ((ctx, status), OpenGoals)) | Proofmode (v, ty, t, []) ->
    let ctx, () = EC.push_const v (ty, if transparent then Some t else None) ctx in
    let r = let u, ty, t = EC.find_const v ctx in Some (Serialized.Define (v, u, ty, t)) in
    (EC.reset ctx, Idle), r)
  | Hint (pat, hint) ->
    let* pat = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate ~evars_with_ctx:false pat)) in
    let* pat = Context.Monad.of_engine (EC.Monad.to_mut (E.to_pattern pat)) in 
    fun (ctx, status) -> ({ ctx with hints = Engine.Pattern.Map.add pat hint ctx.hints }, status), Some (Serialized.Hint (pat, hint))
  | Whd t ->
    let** ctx = fun (ctx, _) -> ctx in
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.whd t)) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.print t')) in
    let () = print_endline ("whd " + t + " := " + t') in
    (* Do not forget to restore the context. *)
    fun (_, status) -> (ctx, status), None
  | Eval t ->
    let** ctx = fun (ctx, _) -> ctx in
    let* t = Context.Monad.of_engine (PC.Monad.to_engine (P.elaborate t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.eval t)) in
    let* t = Context.Monad.of_engine (EC.Monad.to_mut (E.print t)) in
    let* t' = Context.Monad.of_engine (EC.Monad.to_mut (E.print t')) in
    let () = print_endline ("eval " + t + " := " + t') in
    (* Do not forget to restore the context. *)
    fun (_, status) -> (ctx, status), None
  | Skip -> ret None
  | Import file ->
    let serialized = List.of_json (fun j ->
        match List.hd (Yojson.Basic.Util.keys j) with
        | "name" -> Serialized.Define (String.of_json (Yojson.Basic.Util.member "name" j), Kernel.Univ.Context.of_json (Yojson.Basic.Util.member "univ" j), Kernel.Term.of_json (Yojson.Basic.Util.member "type" j), Option.of_json Kernel.Term.of_json (Yojson.Basic.Util.member "body" j))
        | "pattern" -> Serialized.Hint (Engine.Pattern.of_json (Yojson.Basic.Util.member "pattern" j), String.of_json (Yojson.Basic.Util.member "tactic" j))
        | _ -> raise (Invalid_argument "Import")
      ) (Yojson.Basic.from_file file) in
    let+ _ = Context.Monad.of_engine (EC.Monad.List.map (function
      | Serialized.Define (v, u, ty, t) -> fun ctx -> E.{ ctx with const = SMap.add v (u, ty, t) ctx.const }, ()
      | Serialized.Hint (pat, tac) -> fun ctx -> E.{ ctx with hints = Engine.Pattern.Map.add pat tac ctx.hints }, ()
    ) serialized) in
    None (* TODO: add a check preventing several imports of the same file. *)
  | Set (flag, value) -> fun (ctx, status) ->
    let ctx, () = EC.add_flag flag value ctx in
    (ctx, status), None
  | Unset flag -> fun (ctx, status) ->
    let ctx, () = EC.remove_flag flag ctx in
    (ctx, status), None
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
  | AlreadyDefined v -> v ^ " is already defined."
