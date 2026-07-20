Import "test/rw.vo".

(* Common datatypes. *)

(* Equality *)

Definition eq {A : Type} (a : A) : A -> Type :=
  ind eq : A -> Type | eq a end.

Definition eq_refl {A} {a : A} := (eq a).mk(0).

Hint "refine eq_refl" for @eq _ _ _.

Definition eq_sym {A} {a b : A} : eq a b -> eq b a.
Proof. case. apply eq_refl. Qed.

Definition eq_trans {A} {b a c : A} : eq a b -> eq b c -> eq a c.
Proof. case. apply. Qed.

Definition Symmetric_eq {T} : Symmetric (@eq T).
Proof. apply @eq_sym. Qed.

Hint "exact Symmetric_eq" for @Symmetric _ (@eq _).

Definition eq_RwRel {I T} (RT : T -> T -> Type) (f : I -> T) (x y : I) {RT_refl : Reflexive RT} : @RwRel I T (@eq I) RT f x y.
Proof. case. exact (RT_refl (f x)). Qed.

Hint "refine (eq_RwRel _ _ _ _)" for @RwRel _ _ (@eq _) _ _ _ _.

Definition eqfun {I T} (f : I -> T) (x y : I) : eq x y -> eq (f x) (f y).
Proof. case. apply eq_refl. Qed.

(* Logical combinators *)

Definition prod T U := ind prod : Type | T -> U -> prod end.
Definition pair {T U} : T -> U -> prod T U := (prod T U).mk(0).
Definition fst {T U} (x : prod T U) : T := match x return fun x => T with | pair t u => t end.
Definition snd {T U} (x : prod T U) : U := match x return fun x => U with | pair t u => u end.
Definition and := prod.

Definition prodC {T U} (x : prod T U) : prod U T := match x return fun x => prod U T with | (prod T U).mk(0) t u => pair u t end.
Definition prodA {T U V} (x : prod T (prod U V)) : prod (prod T U) V :=
  match x with | pair t uv =>
  match uv with | pair u v =>
  pair (pair t u) v end end.

Definition RwRel_impl_prod {I} (RI : I -> I -> Type) (f g : I -> Type) (x y : I) : @RwRel I Type RI impl f x y -> @RwRel I Type RI impl g x y -> @RwRel I Type RI impl (fun x => prod (f x) (g x)) x y.
Proof.
intros fP gP xy fg.
exact (pair (fP xy (fst fg)) (gP xy (snd fg))).
Qed.

Hint "refine (RwRel_impl_prod _ _ _ _ _ _ _)" for @RwRel _ _ _ impl (fun x => prod _ _) _ _.

Definition sum T U := ind sum : Type | T -> sum | U -> sum end.
Definition inl {T U} : T -> sum T U := (sum T U).mk(0).
Definition inr {T U} : U -> sum T U := (sum T U).mk(1).
Definition or := sum.

Definition sumC {T U} (x : sum T U) : sum U T :=
  match x with
  | inl t => inr t
  | inr u => inl u
  end.

Definition sumA {T U V} (x : sum T (sum U V)) : sum (sum T U) V :=
  match x with
  | inl t => inl (inl t)
  | inr uv =>
    match uv with
    | inl u => inl (inr u)
    | inr v => inr v
    end
  end.

Definition RwRel_impl_or {I} (RI : I -> I -> Type) (f g : I -> Type) (x y : I) : @RwRel I Type RI impl f x y -> @RwRel I Type RI impl g x y -> @RwRel I Type RI impl (fun x => sum (f x) (g x)) x y.
Proof.
intros fP gP xy fg.
exact (match fg with
  | inl fy => inl (fP xy fy)
  | inr gy => inr (gP xy gy)
  end).
Qed.

Hint "refine (RwRel_impl_prod _ _ _ _ _ _ _)" for @RwRel _ _ _ impl (fun x => sum _ _) _ _.

Definition empty := ind empty : Type end.

Definition False := empty.

Definition FalseE {P} : False -> P. Proof. case. Qed.

Hint "exact FalseE" for False -> _.

Definition not T := T -> False.

Definition unit := ind unit : Type | unit end.
Definition tt := (unit).mk(0).
Hint "exact tt" for unit.

Definition True := unit.
Hint "exact tt" for True.

Definition iff T U := prod (T -> U) (U -> T).

Definition Reflexive_iff : Reflexive iff.
Proof. intros T. exact (pair id id). Qed.

Hint "exact @Reflexive_iff" for Reflexive iff.

Definition Symmetric_iff : Symmetric iff.
Proof. intros T U. apply prodC. Qed.

Hint "exact @Symmetric_iff" for Symmetric iff.

Definition RwRel_iff_sub_impl (T U : Type) : @RwRel Type Type iff impl (fun x => x) T U.
Proof. apply fst. Qed.

Hint "refine (@RwRel_iff_sub_impl _ _)" for @RwRel _ _ iff impl (fun x => x) _ _.

Definition RwRel_impl_iff {I} (RI : I -> I -> Type) (f g : I -> Type) (x y : I) : @RwRel I Type RI iff f x y -> @RwRel I Type RI iff g x y -> @RwRel I Type RI impl (fun x => iff (f x) (g x)) x y.
Proof.
intros fP gP xy fgx.
apply pair.
  intros fy.
  apply (fst (gP xy)).
  apply (fst fgx).
  apply (snd (fP xy)).
  exact fy.
intros gy.
apply (fst (fP xy)).
apply (snd fgx).
apply (snd (gP xy)).
exact gy.
Qed.

Hint "refine (@RwRel_impl_iff _ _ _ _ _ _ _ _)" for @RwRel _ _ _ impl (fun x => iff _ _) _ _.

Definition RwRel_iff_impl {I} (RI : I -> I -> Type) (f : I -> Type) (x y : I) : @RwRel I Type RI impl f x y -> @RwRel I Type RI (swap_rel impl) f x y -> @RwRel I Type RI iff f x y.
Proof.
intros fxy fyx xy. apply pair.
  exact (fxy xy).
exact (fyx xy).
Qed.

Hint "refine (@RwRel_iff_sub_impl _ _ _ _ _ _ _)" for @RwRel _ _ _ iff _ _ _.

Definition andTp {P} : iff (and True P) P.
Proof.
apply pair.
  apply snd.
apply (pair tt).
Qed.

Hint "refine (andTp _)" for and True _.
  
Definition andpT {P} : iff (and P True) P.
Proof.
apply pair.
  apply fst.
intro p. exact (pair p tt).
Qed.

Hint "refine (andpT _)" for and _ True.

Definition andFp {P} : iff (and False P) False.
Proof.
apply pair.
  apply fst.
apply FalseE.
Qed.

Definition andpF {P} : iff (and P False) False.
Proof.
apply pair.
  apply snd.
apply FalseE.
Qed.

Definition andpp {P} : iff (and P P) P.
Proof.
apply pair.
  apply fst.
intro p. exact (pair p p).
Qed.

Definition orTp {P} : iff (or True P) True.
Proof.
apply pair; intro x.
  exact tt.
exact (inl tt).
Qed.

Definition orpT {P} : iff (or P True) True.
Proof.
apply pair; intro x.
  exact tt.
exact (inr tt).
Qed.

Definition orFp {P} : iff (or False P) P.
Proof.
apply pair.
  case.
    apply FalseE.
  apply.
apply inr.
Qed.

Definition orpF {P} : iff (or P False) P.
Proof.
apply pair.
  case.
    apply.
  apply FalseE.
apply inl.
Qed.

Definition orpp {P} : iff (or P P) P.
Proof.
apply pair.
  case; apply.
apply inl.
Qed.

Definition or_andl {P Q R} : iff (or (and P Q) R) (and (or P R) (or Q R)).
Proof.
apply pair.
  case.
    intro pq.
    apply pair, inl.
      exact (fst pq).
    exact (snd pq).
  intro r. apply pair, inr, r.
case. case.
  intro p. case.
    intro q. apply inl, pair.
      exact p.
    exact q.
  intro r. apply inr, r.
intro r qr. apply inr, r.
Qed.

Definition or_andr {P Q R} : iff (or P (and Q R)) (and (or P Q) (or P R)).
Proof.
apply pair.
  case.
    intro p. apply pair, inl, p.
  intro qr.
  apply pair, inr.
    exact (fst qr).
  exact (snd qr).
case. case.
  intro p pr. apply inl, p.
intro q. case.
  intro p. apply inl, p.
intro r. apply inr, pair.
  exact q.
exact r.
Qed.

(* TODO: more logic lemmas. *)

Definition iff_trans {T U V} : iff U T -> iff T V -> iff U V.
Proof.
intros UT.
rw UT.
apply id.
Qed.

(* Existential quantifier *)

Definition ex {T} (P : T -> Type) := ind ex : Type | forall (x : T), P x -> ex end.
(* TODO: Find better names? *)
Definition ex_intro {T} {P} := (@ex T P).mk(0).
(* TOTHINK: The type annotation is required because typing the branch of the match can not instantiate the return type of said match, which at this point is a hole applied to `ex_intro x p`, which is HO. However, the type of `x` is `T`, which unless I am mistaken can not non-trivially be obtained from `ex_intro x p`, so maybe we can ignore the argument. *)
Definition ex_proj1 {T} {P} (x : @ex T P) : T := match x with | ex_intro x p => x end.
(* TODO: Here, without the return type of the match, I have the following equations:
  `?15 T P x x =~= P (ex_proj1@{s_5, s_6;u_6, u_7, u_8, u_9, u_10} (?4 T P x) (?5 T P x) x)
  ?15 T P x (ind.mk(ind ex : s_12@{u_16} := | forall (x00 : T) (_ : P x00), ex).0 x0 p) =~= P x0`
   There is only one solution, considering that the second equation forbids the use of the 3rd argument of `?15`. *)
Definition ex_proj2 {T} {P} (x : @ex T P) : P (ex_proj1 x) := match x return fun x => P (ex_proj1 x) with | ex_intro x p => p end.

