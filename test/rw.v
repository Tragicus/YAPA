(* Datatypes and basic results related to the `rw` tactic. *)

(* Properties of relations *)

Definition Reflexive {T} (R : T -> T -> Type) := forall x, R x x.

Definition swap_rel {T U} (R : T -> U -> Type) x y := R y x.

Definition Reflexive_swap_rel {T} (R : T -> T -> Type) : Reflexive R -> Reflexive (swap_rel R).
Proof. intros RR x. apply RR. Qed.

Hint "refine (Reflexive_swap_rel _ _)" for @Reflexive _ (@swap_rel _ _ _).

Definition Symmetric {T} (R : T -> T -> Type) := forall {x y}, R x y -> swap_rel R x y.

(* The tactic `rw` applied to `r : RI x y` on a goal `g` works by abstracting `x` in `g`, i.e. finding `f` such that `g = f x` and synthesising a proof of `@RwRel _ _ RI (swap_rel impl) f x y`. *)

Definition impl T U := T -> U.

Definition Reflexive_impl : Reflexive impl.
Proof. intro T. apply. Qed.

Hint "exact Reflexive_impl" for Reflexive impl.

Definition RwRel {I T} {RI : I -> I -> Type} {RT : T -> T -> Type} (f : I -> T) (x y : I) := RI x y -> RT (f x) (f y).

(* If the LHS does not occur in a subpart of the goal, then rewriting is possible as soon as the expected relation at this point it reflexive. *then rewriting is possible as soon as the expected relation at this point it reflexive. *)
Definition RwRel_forget {I T} {RI : I -> I -> Type} {RT : T -> T -> Type} (t : T) (x y : I) {RT_refl : Reflexive RT} : @RwRel I T RI RT (fun x => t) x y.
Proof. intros z. apply RT_refl. Qed.

Hint "refine (RwRel_forget _ _ _)" for @RwRel _ _ _ _ (fun x => _) _ _.

(* We can move a `swap_rel` from the target relation to the input one. *)
Definition RwRel_sym {I T} {RI : I -> I -> Type} {RT : T -> T -> Type} (f : I -> T) (x y : I) : @RwRel I T (swap_rel RI) RT f y x -> @RwRel I T RI (swap_rel RT) f x y.
Proof. apply. Qed.

Hint "refine (RwRel_sym _ _ _ _)" for @RwRel _ _ _ (@swap_rel _ _ _) _ _ _.

(* We can get rid of a `swap_rel` on a symmetric input relation. *)
Definition RwRel_Symmetric_sym {I T} {RI : I -> I -> Type} {RT : T -> T -> Type} (f : I -> T) (x y : I) {RI_sym : Symmetric RI} : @RwRel I T RI RT f y x -> @RwRel I T (swap_rel RI) RT f y x.
Proof. intros fP xy. exact (fP (RI_sym xy)). Qed.

Hint "refine (RwRel_Symmetric_sym _ _ _ _)" for @RwRel _ _ (@swap_rel _ _ _) _ _ _ _.

(* We can get rid of two `swap_rel` on the input relation. *)
Definition RwRel_swapKl {I T} {RI : I -> I -> Type} {RT : T -> T -> Type} (f : I -> T) (x y : I) : @RwRel I T RI RT f y x -> @RwRel I T (swap_rel (swap_rel RI)) RT f y x.
Proof. apply. Qed.

Hint "refine (RwRel_swapKl _ _ _ _)" for @RwRel _ _ (@swap_rel _ _ (@swap_rel _ _ _)) _ _ _ _.

Definition id {T} (x : T) := x.

(* We can copy the input relation to the output when the part of the goal under consideration is exactly the LHS. *)
Definition RwRel_id {T} {RT : T -> T -> Type} (x y : T) : @RwRel T T RT RT (fun x => x) x y.
Proof. apply id. Qed.

Hint "refine (RwRel_id _ _)" for @RwRel _ _ _ _ (fun x => x) _ _.

(* Compatibility of implication. *)
Definition RwRel_impl_impl {I} (RI : I -> I -> Type) (f g : I -> Type) (x y : I) : @RwRel I Type RI (swap_rel impl) f x y -> @RwRel I Type RI impl g x y -> @RwRel I Type RI impl (fun x => (f x) -> (g x)) x y.
Proof.
intros fP gP xy fgx fy.
exact (gP xy (fgx (fP xy fy))).
Qed.

Hint "refine (RwRel_impl_impl _ _ _ _ _ _ _)" for @RwRel _ _ _ impl (fun x => impl _ _) _ _.
Hint "refine (RwRel_impl_impl _ _ _ _ _ _ _)" for @RwRel _ _ _ impl (fun x => _ -> _) _ _.
