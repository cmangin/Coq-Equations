Require Import Program Equations.Equations.

Inductive ilist (A : Set) : nat -> Set :=
| Nil : ilist A 0
| Cons : forall {n}, A -> ilist A n -> ilist A (S n).
Arguments Nil [A].
Arguments Cons [A n _ _].

Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).

Equations fin_to_nat {n : nat} (i : fin n) : nat :=
fin_to_nat fz := 0;
fin_to_nat (fs j) := S (fin_to_nat j).

Lemma fin_lt_n : forall (n : nat) (i : fin n), fin_to_nat i < n.
Proof.
  intros. funelim (fin_to_nat i).
    - apply Le.le_n_S; apply Le.le_0_n.
    - apply Lt.lt_n_S; assumption.
Defined.

Equations nat_to_fin {n : nat} (m : nat) (p : m < n) : fin n :=
nat_to_fin {n:=(S n)} 0 _ := fz;
nat_to_fin {n:=(S n)} (S m) p := fs (nat_to_fin m _).

Next Obligation. apply Lt.lt_S_n; assumption. Defined.

(*
Equations fin_to_nat {n : nat} (i : fin n) : {m : nat | m < n} :=
fin_to_nat _ fz := exist _ 0 _;
fin_to_nat _ (fs j) := let (m, p) := fin_to_nat j in exist _ (S m) _.
Next Obligation. apply Le.le_n_S; apply Le.le_0_n. Defined.
Next Obligation. apply Lt.lt_n_S; assumption. Defined.

(*
Equations nat_to_fin {n : nat} (m : nat) (p : m < n) : fin n :=
nat_to_fin (S n) 0 _ := fz;
nat_to_fin (S n) (S m) _ := fs (nat_to_fin m _).
Next Obligation. apply Lt.lt_S_n; assumption. Defined.
*)


Equations nat_to_fin {n : nat} (m : {m : nat | m < n}) : fin n :=
nat_to_fin 0 m :=! m;
nat_to_fin (S n) (exist ?(fun m => m < S n) 0 _) := fz;
nat_to_fin (S n) (exist ?(fun m => m < S n) (S m) _) := fs (nat_to_fin (exist _ m _)).
*)
(*
nat_to_fin (S n) m <= proj1_sig m => {
  nat_to_fin (S n) m 0 := fz;
  nat_to_fin (S n) m (S m') := fs (nat_to_fin (exist _ m' _))
}.
Obligation Tactic := idtac.
Next Obligation. intros.
*)
(*
nat_to_fin (S n) m <= m => {
  nat_to_fin (S n) m (exist _ 0 _) := fz;
  nat_to_fin (S n) m (exist _ (S m') _) := fs (nat_to_fin (exist _ m' _ ))
}.
*)

Lemma fin__nat : forall (n : nat) (m : nat) (p : m < n),
  fin_to_nat (nat_to_fin m p) = m.
Proof.
  intros.
  funelim (fin_to_nat (nat_to_fin m p));
  funelim (nat_to_fin m p).
    - reflexivity.
    - inversion H1.
    - inversion H1.
    - clear H. f_equal. simp fin_to_nat in H2. noconf H2. rewrite H. 
      apply H1; auto. inversion H3. apply inj_pair2 in H4. subst; reflexivity.
Qed.

Lemma nat__fin : forall (n : nat) (i : fin n),
  nat_to_fin (fin_to_nat i) (fin_lt_n n i) = i.
Proof.
  intros.
  funelim (nat_to_fin (fin_to_nat i) (fin_lt_n n i));
  funelim (fin_to_nat i).
    - reflexivity.
    - inversion H1.
    - inversion H1.
    - clear H. subst call0. unfold nat_to_fin_obligation_1 in *. f_equal.
        simp fin_to_nat in H3. noconf H3.
        replace (Lt.lt_S_n (fin_to_nat f) n0 (fin_lt_n (S n0) (fs f))) with (fin_lt_n n0 f) in * by (apply proof_irrelevance).
        apply H1; reflexivity.
Qed.

Equations iget {A : Set} {n : nat} (l : ilist A n) (i : fin n) : A :=
iget {n:=(S n)} (Cons x _) fz := x;
iget {n:=(S n)} (Cons _ t) (fs j) := iget t j.

Equations isnoc {A : Set} {n : nat} (l : ilist A n) (x : A) : ilist A (S n) :=
isnoc Nil x := Cons x Nil;
isnoc (Cons y t) x := Cons y (isnoc t x).

Lemma append_get : forall (A : Set) (n : nat) (l : ilist A n) (x : A),
  iget (isnoc l x) (nat_to_fin n (Lt.lt_n_Sn n)) = x.
Proof.
  induction n ; intros.
    - depelim l. simp isnoc nat_to_fin iget.
    - depelim l. simp isnoc nat_to_fin iget.
      unfold nat_to_fin_obligation_1.
      replace (Lt.lt_S_n n (S n) (Lt.lt_n_Sn (S n))) with (Lt.lt_n_Sn n) by (apply proof_irrelevance).
      apply IHn.
Qed.

Definition convert_ilist {A : Set} {n m : nat} (p : n = m) (l : ilist A n) : ilist A m.
Proof. rewrite <- p. assumption. Defined.

Lemma convert_ilist_trans : forall {A : Set} {n m o : nat} (p : n = m) (r : m = o) (l : ilist A n),
  convert_ilist r (convert_ilist p l) = convert_ilist (eq_trans p r) l.
Proof. intros. simplify_eqs. reflexivity. Qed.

Equations irev_aux {A : Set} {i j : nat} (l : ilist A i) (acc : ilist A j) : ilist A (i + j) :=
irev_aux Nil acc := acc;
irev_aux (Cons x t) acc := convert_ilist _ (irev_aux t (Cons x acc)).

Program Definition irev {A : Set} {n : nat} (l : ilist A n) : ilist A n := irev_aux l Nil.

Ltac match_refl :=
match goal with
| [ |- context[ match ?P with _ => _ end ] ] => rewrite UIP_refl with (p := P)
end.

Example rev_ex : forall (A : Set) (x y : A), irev (Cons x (Cons y Nil)) = Cons y (Cons x Nil).
Proof.
  intros.
  unfold irev; simp irev_aux.
  compute; repeat match_refl; reflexivity.
Qed.

Equations iapp {A : Set} {n m : nat} (l1 : ilist A n) (l2 : ilist A m) : ilist A (n + m) :=
iapp Nil l := l;
iapp (Cons x t) l := Cons x (iapp t l).


Lemma iapp_cons : forall (A : Set) (i j : nat) (l1 : ilist A i) (l2 : ilist A j) (x : A),
  iapp (Cons x l1) l2 = Cons x (iapp l1 l2).
Proof. simp iapp. Qed.

Definition rev_aux_app_stmt := forall (A : Set) (i j1 j2 : nat) (l : ilist A i)
  (acc1 : ilist A j1) (acc2 : ilist A j2) H,
  convert_ilist H (irev_aux l (iapp acc1 acc2)) = iapp (irev_aux l acc1) acc2.

Lemma rev_aux_app : rev_aux_app_stmt.
Proof.
  unfold rev_aux_app_stmt.
  intros.
  funelim (irev_aux l acc1).
    - simp irev_aux iapp. compute; match_refl; reflexivity.
    - simp irev_aux iapp. rewrite convert_ilist_trans.
      rewrite <- iapp_cons.
      set (He := eq_trans _ _). clearbody He.
      set (He' := irev_aux_obligation_1 _ _ _ _ _ _ _). clearbody He'.
Admitted.

Equations irev' {A : Set} {n : nat} (l : ilist A n) : ilist A n :=
irev' Nil := Nil;
irev' (Cons x t) := isnoc (irev' t) x.

Lemma isnoc_irev A n a (l : ilist A n) : isnoc (irev l) a = irev (Cons a l).
Proof.
  unfold irev. symmetry. 
Admitted.

Lemma rev__rev' : forall (A : Set) (i : nat) (l : ilist A i), irev l = irev' l.
Proof.
  intros.
  funelim (irev' l). unfold irev. simplify_eqs. simp irev_aux.
  unfold irev.
Admitted.
  
Equations rev_range (n : nat) : ilist nat n :=
rev_range 0 := Nil;
rev_range (S n) := Cons n (rev_range n).

Equations(noind) negb (b : bool) : bool :=
negb true := false;
negb false := true.

Inductive fle : forall {n}, fin n -> fin n -> Set :=
| flez : forall {n j}, @fle (S n) fz j
| fles : forall {n i j}, fle i j -> @fle (S n) (fs i) (fs j).

Equations fin0_empty (i : fin 0) : False :=
fin0_empty i :=! i.

Equations(nocomp) fle_trans {n : nat} {i j k : fin n} (p : fle i j) (q : fle j k) : fle i k :=
fle_trans flez _ := flez;
fle_trans (fles p') (fles q') := fles (fle_trans p' q').
Print Assumptions fle_trans.

Derive Signature for fin.
Derive NoConfusion for fin.
Derive DependentElimination for fin.

From Equations Require Import EqDec DepElimDec.

Derive Signature for @fle.
Derive NoConfusion for @fle.


Ltac eqdec_proof ::= try red; intros;
  match goal with
    |- dec_eq ?x ?y =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- dec_eq ?x ?y => eqdec_loop x y
    end
   | |- { ?x = ?y } + { _ } =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- { ?x = ?y } + { _ } => eqdec_loop x y
    end
  end.
(* FIXME references are wrong if we don't redefine here ... *)
Derive Equality for @fin.
Solve Obligations with eqdec_proof.

Derive Equality for @fle.
Solve Obligations with eqdec_proof.

Derive Subterm for @fle.

Equations fle_trans' {n : nat} {i j : fin n} (p : fle i j) {k} (q : fle j k) : fle i k :=
fle_trans' p q by rec p (@fle_subterm) :=
fle_trans' flez _ := flez;
fle_trans' (fles p') (fles q') := fles (fle_trans' p' q').

Print Assumptions fle_trans'.

(*
x.

From Equations Require Import DepElimDec.
Derive Signature for @eq.

Inductive eqP {A : Type} {B : A -> Type} (a b : A) (t : B a) : B b -> Prop :=
  idpath_over (p : a = b) : eqP a b t (eq_rect a B t b p).

Lemma eq_rect_eqP {A : Type} {B : A -> Type} (a b : A) (p : a = b) (t : B a) (u : B b) :
  eq_rect a B t b p = u -> eqP a b t u.
Proof.
  intros. rewrite <- H. constructor.
Defined.  

Lemma eqP_eq_rect {A : Type} {B : A -> Type} (a b : A) (p : a = b) (t : B a) (u : B b) :
  eqP a b t u -> eq_rect a B t b p = u.
Proof.
  intros. destruct H. destruct p. simpl. revert p0. simplify_dep_elim. reflexivity.
Defined.  

Notation "x =~ y" := (eqP _ _ x y) (at level 90, format " x  =~  y ").

Lemma eqP_eq_rect_l {A : Type} {B : A -> Type} (a b c : A)
      (p : a = b) (q : b = c) (t : B a) (v : B c) :
  t =~ v -> eq_rect _ B t _ p =~ v.
Proof.
  intros. destruct p, q. now simpl in *.
Defined. 

(* Notation " x =_  y " := (eqP _ _ _ x y) (at level 90). *)
*)