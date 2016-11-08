Require Import Equations.Equations.
Require Import Equations.DepElim.
Require Import Equations.DepElimDec.

Class Generalization {A : Type} (x : A) := {
  generalization_ty : Type;
  generalization : generalization_ty
}.

Inductive foo : nat -> nat -> Type := .
Derive Signature for foo.

Instance fin_generalization : forall (n m : nat) (f : foo n m), Generalization f := {
  generalization_ty := _;
  generalization := _
}.
Proof.
  on_last_hyp ltac:(fun id =>
      let ty := type of id in
      let P := fresh "P" in
      let H := fresh "H" in
      refine (forall (P : foo n m -> Type) (H : _), P f)
    ).
  refine (forall (n' m' : nat) (f' : foo n' m'), _).
  let v := eval hnf in (signature_pack f) in
  let v' := eval hnf in (signature_pack f') in
  exact (v = v' -> P f).
  intros P H; eapply H; reflexivity.
Defined.

Goal forall n (P : forall n, foo n n -> Type) (f : foo n n), P _ f.
Proof.
  intros.
  revert P.
  assert (forall (T : Type), T -> T -> T) as X by auto; apply X; clear X.
  generalize_by_eqs f. destruct f.
  set (gen := @generalization _ f _); clearbody gen; apply gen; clear gen; intros until 0; revert f; rename f' into f.
   apply gen; clear gen; compute;
  intros n' m' f'; revert f; rename f' into f.
  destruct f.
  
  ∀ f0 : foo n n, ((n; n); f0) = ((f''; f'); f) → ∀ P : ∀ n0 : nat, foo n0 n0 → Type, P n f0
  ∀ f0 : foo n n, ((n; n); f0) = ((n'; m'); f) → ∀ P : ∀ n0 : nat, foo n0 n0 → Type, P n f0