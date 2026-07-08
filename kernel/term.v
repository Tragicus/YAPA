From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq.

Section Term.
Variable (VarType : Type).
Inductive head :=
  | Var of nat
  | Const of 
