From mathcomp Require Import ssreflect ssrbool ssrfun seq.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Unset Printing Implicit Defensive.

Declare Scope monad_scope.
Delimit Scope monad_scope with M.
Local Open Scope monad_scope.

Module Monad.

Definition t S T := S -> S * T.
Definition it S T := S -> T.

Definition ret S T x : t S T := fun ctx => (ctx, x).
Definition iret S T x : it S T := fun=> x.

Definition to_mut S T (state : it S T) : t S T := fun ctx => (ctx, state ctx).
Definition to_imut S T (state : t S T) : it S T := fun ctx => (state ctx).2.

Definition bind S T U (state : t S T) (f : T -> S -> U) : S -> U := fun ctx =>
  match state ctx with | (ctx, x) => f x ctx end.
Definition ibind S T U (state : it S T) (f : T -> S -> U) : S -> U := fun ctx =>
  f (state ctx) ctx.

Definition map S T U (state : t S T) (f : T -> U) : t S U := fun ctx =>
  match state ctx with | (ctx, x) => (ctx, f x) end.
Definition imap S T U (state : it S T) (f : T -> U) : it S U := f \o state.

Module Notations.
Notation " 'let*' x ':=' y 'in' z " := (bind y (fun x => z)) (at level 1, x binder, z at level 200).
Notation " 'let**' x ':=' y 'in' z " := (ibind y (fun x => z)) (at level 1, x binder, z at level 200).
Notation " 'let+' x ':=' y 'in' z " := (map y (fun x => z)) (at level 1, x binder, z at level 200).
Notation " 'let+*' x ':=' y 'in' z " := (imap y (fun x => z)) (at level 1, x binder, z at level 200).
End Notations.

Import Notations.

Module List.

Definition map S T U (f : T -> t S U) (s : seq T) : t S (seq U) :=
  let+ s := fun ctx => foldl (fun state x =>
    match state with
    | (ctx, s) => (let+ y := f x in y :: s) ctx
    end) (ctx, [::]) s in
  rev s.

Fixpoint all S T (f : T -> t S bool) (s : seq T) : t S bool :=
  match s with
  | [::] => ret true
  | x :: s =>
    let* b := f x in
    if b then all f s else ret b
  end.

Fixpoint has S T (f : T -> t S bool) (s : seq T) : t S bool :=
  match s with
  | [::] => ret false
  | x :: s =>
    let* b := f x in
    if b then ret b else has f s
  end.

Fixpoint fold_left S T U (f : T -> U -> t S U) (s : seq T) (acc : U) : t S U :=
  match s with
  | [::] => ret acc
  | x :: s =>
    let* acc := f x acc in
    fold_left f s acc
  end.
End List.

Module Option.
Definition map S T U (f : T -> t S U) (x : option T) : t S (option U) :=
  match x with | None => ret None | Some x => let+ x := f x in Some x end.

Definition bind S T U (x : t S (option T)) (f : T -> t S (option U)) :=
  let* x := x in
  match x with | None => ret None | Some x => f x end.
End Option.

End Monad.
Export Notations.
