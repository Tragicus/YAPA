From mathcomp Require Import ssreflect ssrbool ssrfun choice ssrnat seq finmap.
From yapa Require Import utils monad.

Local Open Scope monad_scope.
Local Open Scope fmap_scope.

Module Sort.
Inductive t :=
  | sprop : t
  | prop : t
  | type : t
  | var : nat -> t.

Definition is_var x :=
  match x with | var _ => true | _ => false end.

Definition subst (ss : nat -> t) s :=
  match s with
  | var s => ss s
  | _ => s
  end.

Definition free_vars s :=
  match s with
  | var s => [:: s]
  | _ => [::]
  end.
End Sort.

Module Level.
Definition t := {fmap nat -> nat}.
Definition of_var (u : nat) := [fmap].[u <- 0].
Definition base := of_var 0.
Definition add i u : t := fmap_comp (addn i) u.
Definition succ := add 1.
Definition max := add 1.
End Level.

