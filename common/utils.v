From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq preorder finfun finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.

(*
Declare Scope map_scope.
Delimit Scope map_scope with map.
Local Open Scope map_scope.

Module Map.
Section Map.
Variable (disp : _) (T : preorderType disp) (V : Type).

Definition t := list (T * V).

Implicit Types (i : T) (v : V) (m : t).

Definition empty : t := [::].
Definition singleton i v : t := [:: (i, v)].

Definition add i v : t -> t := cons (i, v).
Definition remove i : t -> t := filter (fun j => fst j != i).
Fixpoint find m i :=
  match m with
  | [::] => None
  | (j, v) :: m => if j == i then Some v else find m i
  end.
End Map.

Module Exports.
Notation "{}" := (@empty _ _ _) : map_scope.
Notation " m '[' x '->' v ']' " := (add x v m)
 *)

Definition compf (T : choiceType) U V (g : U -> V) (f : {fmap T -> U}) :=
  [fmap x : domf f => g (ffun_of_fmap f x)].

Lemma compfE T U V g f x : (@compf T U V g f).[? x] = omap g (f.[? x]).
Proof.
case: (fndP _ _) => /= [|/negP] xf; case: (fndP _ _) => [|/negP] //= xf'.
by rewrite ffunE; congr (Some (g (f _))); apply: val_inj.
Qed.

Definition ocollectf_subdef (T : choiceType) U (f : {fmap T -> option U}) :=
  [fset x in domf f | match f.[? x] with | Some None => false | _ => true end].

Definition ocollectf_subproof_subdef T (x : option T) :=
  match x with
  | None => False
  | _ => True
  end.

Lemma ocollectf_subproof (T : choiceType) U (f : {fmap T -> option U}) (x : ocollectf_subdef f) :
  ocollectf_subproof_subdef (f (fincl (fset_sub _ _) x)).
Proof.
rewrite /ocollectf_subproof_subdef.
move: (valP x); rewrite /ocollectf_subdef inE/= => /andP[] _.
set x0 := (fincl _ _).

Definition ocollectf (T : choiceType) U (f : {fmap T -> option U}) : {fmap T -> U} :=
  [fmap x : ocollectf_subdef f =>
    match f (fincl (fset_sub _ _) x) as y return (f (fincl (fset_sub _ _) x) = y -> U) with
    | Some y => fun=> y
    | None => fun e => False_rec _ (eq_ind _ ocollectf_subproof_subdef (ocollectf_subproof x) _ e)
    end erefl].


Definition fmap_merge (T : choiceType) U V W (j : T -> option U -> option V -> option W) (f : {fmap T -> U}) (g : {fmap T -> V}) :=
  
  

Lemma unionf_subdef (T : choiceType) (A B : {fset T}) (x : T) : x \in A `|` B -> x \notin A -> x \in B.
Proof. by rewrite inE => /orP[]// + /negP. Qed.

Definition fmap_union (T : choiceType) U (j : T -> U -> U -> option U) (f : {fmap T -> U}) (g : {fmap T -> U}) :=
  [fmap x : domf f `|` domf g =>
    match fndP f (val x) with
    | FndIn xf =>
      match fndP g (val x) with
      | FndIn xg => j (val x) f.[xf] g.[xg]
      | FndOut _ => f.[xf]
      end
    | FndOut xf => g [` fmap_union_subdef (valP x) xf]
    end].

Lemma fmap_unionE (T : choiceType) U (j : T -> U -> U -> U) (f : {fmap T -> U}) (g : {fmap T -> U}) (x : T)

  

