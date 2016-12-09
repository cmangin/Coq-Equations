Require Import Equations.Equations.
Require Import Equations.DepElimDec.

Class Generalization {A : Type} (x : A) := {
  generalization_ty : Type -> Type;
  generalization : forall (P : Type), generalization_ty P
}.

Hint Extern 0 (@Generalization ?A ?x) => custom_generalization : typeclass_instances.
