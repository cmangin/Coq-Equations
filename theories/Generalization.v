Require Import Equations.Equations.
Require Import Equations.DepElimDec.

Class Generalization {A : Type} (x : A) := {
  generalization_ty : Type;
  generalization : generalization_ty
}.

Hint Extern 0 (@Generalization ?A ?x) => custom_generalization : typeclass_instances.
