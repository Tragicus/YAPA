open Utils
module E = Engine.Term
module EC = E.Context
open EC.Monad.Notations

type t = { ctx: E.t E.telescope; goal: int }

let of_evar i = { ctx = []; goal = i }

(* The term that the goal is expected to instantiate. *)
let target g =
  let+* d = EC.depth in
  E.{ hd = Evar g.goal; args = List.rev (List.init d E.mkVar) }

(* Executes `f` in the context where `g` is well-defined. *)
let enter g f ctx =
  let var = ctx.E.var in
  let ctx' = E.{ ctx with var = IMap.of_list (List.mapi (fun i b -> (i, b)) g.ctx) } in
  let t = target g ctx' in
  let ctx, r = f t ctx' in
  E.{ ctx with var }, r

let print ?(debug=false) g ctx =
  let (+) = String.cat in
  EC.Monad.to_imut (EC.fold_telescope ~avoid_capture:false (* Captures are anomalies *) (fun tele (v, ty, t) ->
      let** ty = E.print ~debug ty in
      let+ t = EC.Monad.Option.map (fun t -> EC.Monad.to_mut (E.print ~debug t)) t in
      (v + " : " + ty + (match t with | None -> "" | Some t -> " := " + t)) :: tele
    ) [] g.ctx (fun tele ->
      let** g = target g in
      let* ty = E.typecheck g in
      let** g = E.print ~debug g in
      let** ty = E.print ~debug ty in
      EC.Monad.ret (String.concat "\n" (List.rev tele @ ["\n==========================\n"; g ^ " : " ^ ty]) + "\n")
    )) { ctx with var = IMap.empty }

let collect_goals t =
(*   let** () = let+* t = E.print t in print_endline ("collect_goals " ^ t) in *)
  let rec aux ids t =
    let** t = E.whd ~flags:E.whd_flags_none t in
    let** hd = match t.E.hd with
      | Evar i when not (ISet.mem i ids) ->
        let** body = EC.get_evar_body i in
        if body <> None then EC.Monad.iret ([], ids) else
        let** d = EC.depth in
        let d = d - 1 in
        let rec process_args k = function | [] -> k | arg :: args ->
          if try let i = E.destVar arg in k = i with _ -> false
          then process_args (k - 1) args
          else k in
        let k = process_args d t.E.args in
        let ids = ISet.add i ids in
        fun ctx -> [{ ctx = List.take (d - k) (List.map snd (IMap.to_list ctx.var)); goal = i }], ids
      | Fun (_, tele, body) ->
        EC.Monad.to_imut (EC.fold_telescope (fun (gs, ids) (_, ty, t) ->
          let** ty, ids = aux ids ty in
          let gs = ty @ gs in
          let+ t = EC.Monad.Option.map (fun t -> EC.Monad.to_mut (aux ids t)) t in
          match t with | None -> gs, ids | Some (t, ids) -> t @ gs, ids
        ) ([], ISet.empty) tele (fun (gs, ids) ->
          let** body, ids = aux ids body in
          EC.Monad.ret (body @ gs, ids)))
      | Ind (v, a, c) ->
        let** a' = aux ids a in
        EC.Monad.to_imut (EC.with_var (v, a, None) (EC.Monad.List.fold_left (fun t (gs, ids) ctx -> let (t, ids) = aux ids t ctx in ctx, (t @ gs, ids)) c a'))
      | Construct (ind, _) | Case (ind, _) -> aux ids ind
      | _ -> EC.Monad.iret ([], ISet.empty) in
    EC.Monad.to_imut (EC.Monad.List.fold_left (fun t (gs, ids) ctx -> let (t, ids) = aux ids t ctx in ctx, (t @ gs, ids)) t.args hd) in
  let+* (gs, _) = aux ISet.empty t in
  List.rev gs
