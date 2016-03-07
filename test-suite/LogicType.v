From Equations Require Import Equations DepElimDec HSets.

Set Universe Polymorphism.

Equations Logic Type Id id_refl Empty unit tt.

Import IdNotations.

Derive Signature for @Id.

Check (_ : HSet nat).

Ltac generalize_sig_dest id ::=
  Id_generalize_sig id ltac:(fun id => decompose_exists id).

Equations test_k (x : nat) (r : x = x) : r = r :=
test_k x id_refl := id_refl.

(* Equations fail_k (A : Type) (x : A) (r : x = x) : r = r := *)
(*   fail_k A x id_refl := id_refl. *)
