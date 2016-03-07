(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Tactics related to (dependent) equality and proof irrelevance. *)

Require Export ProofIrrelevance.
Require Export JMeq.

Require Import Coq.Program.Tactics.
Require Export Equations.Init.
Require Import Equations.Signature.
Require Import Equations.EqDec.
Require Equations.HSets.

Ltac is_ground_goal := 
  match goal with
    |- ?T => is_ground T
  end.

(** Try to find a contradiction. *)

(* Hint Extern 10 => is_ground_goal ; progress (elimtype False). *)

(** We will use the [block] definition to separate the goal from the 
   equalities generated by the tactic. *)

Definition block := tt.

Ltac intros_until_block :=
  match goal with
    |- let _ := block in _ => intros _
  | |- _ => try (intro; intros_until_block)
  end.

Ltac block_goal :=
  match goal with
    | [ |- ?T ] => change (let _ := block in T)
  end.

Ltac unblock_goal := unfold block in *; cbv zeta.

(** Notation for heterogenous equality. *)

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

(** Notation for the single element of [x = x] and [x ~= x]. *)

Implicit Arguments eq_refl [[A] [x]].
Implicit Arguments JMeq_refl [[A] [x]].

(** Do something on an heterogeneous equality appearing in the context. *)

Ltac on_JMeq tac :=
  match goal with
    | [ H : @JMeq ?x ?X ?y ?Y |- _ ] => tac H
  end.

(** Try to apply [JMeq_eq] to get back a regular equality when the two types are equal. *)

Ltac simpl_one_JMeq :=
  on_JMeq ltac:(fun H => apply JMeq_eq in H).

(** Repeat it for every possible hypothesis. *)

Ltac simpl_JMeq := repeat simpl_one_JMeq.

(** Just simplify an h.eq. without clearing it. *)

Ltac simpl_one_dep_JMeq :=
  on_JMeq
  ltac:(fun H => let H' := fresh "H" in
    assert (H' := JMeq_eq H)).

Require Import Eqdep.

(** Simplify dependent equality using sigmas to equality of the second projections if possible.
   Uses UIP. *)

Ltac simpl_existT :=
  match goal with
    [ H : existT _ ?x _ = existT _ ?x _ |- _ ] =>
    let Hi := fresh H in assert(Hi:=inj_pairT2 _ _ _ _ _ H) ; clear H
  | [ H : sigmaI _ ?x _ = sigmaI _ ?x _ |- _ ] =>
    let Hi := fresh H in assert(Hi:=@inj_sigma2 _ _ _ _ _ H) ; clear H
  end.

Ltac simpl_existTs := repeat simpl_existT.

(** Tries to eliminate a call to [eq_rect] (the substitution principle) by any means available. *)

Ltac elim_eq_rect :=
  match goal with
    | [ |- ?t ] =>
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.

(** Rewrite using uniqueness of indentity proofs [H = eq_refl]. *)

Ltac simpl_uip :=
  match goal with
    [ H : ?X = ?X |- _ ] => rewrite (UIP_refl _ _ H) in *; clear H
  end.

(** Simplify equalities appearing in the context and goal. *)

Ltac simpl_eq := simpl ; unfold eq_rec_r, eq_rec ; repeat (elim_eq_rect ; simpl) ; repeat (simpl_uip ; simpl).

(** Try to abstract a proof of equality, if no proof of the same equality is present in the context. *)

Ltac abstract_eq_hyp H' p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
    match tyred with
      ?X = ?Y =>
      match goal with
        | [ H : X = Y |- _ ] => fail 1
        | _ => set (H':=p) ; try (change p with H') ; clearbody H' ; simpl in H'
      end
    end.

(** Apply the tactic tac to proofs of equality appearing as coercion arguments.
   Just redefine this tactic (using [Ltac on_coerce_proof tac ::=]) to handle custom coercion operators.
   *)

Ltac on_coerce_proof tac T :=
  match T with
    | context [ eq_rect _ _ _ _ ?p ] => tac p
  end.

Ltac on_coerce_proof_gl tac :=
  match goal with
    [ |- ?T ] => on_coerce_proof tac T
  end.

(** Abstract proofs of equalities of coercions. *)

Ltac abstract_eq_proof := on_coerce_proof_gl ltac:(fun p => let H := fresh "eqH" in abstract_eq_hyp H p).

Ltac abstract_eq_proofs := repeat abstract_eq_proof.

(** Factorize proofs, by using proof irrelevance so that two proofs of the same equality
   in the goal become convertible. *)

Ltac pi_eq_proof_hyp p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
  match tyred with
    ?X = ?Y =>
    match goal with
      | [ H : X = Y |- _ ] =>
        match p with
          | H => fail 2
          | _ => rewrite (proof_irrelevance (X = Y) p H)
        end
      | _ => fail " No hypothesis with same type "
    end
  end.

(** Factorize proofs of equality appearing as coercion arguments. *)

Ltac pi_eq_proof := on_coerce_proof_gl pi_eq_proof_hyp.

Ltac pi_eq_proofs := repeat pi_eq_proof.

(** The two preceding tactics in sequence. *)

Ltac clear_eq_proofs :=
  abstract_eq_proofs ; pi_eq_proofs.

Hint Rewrite <- eq_rect_eq : refl_id.

(** The [refl_id] database should be populated with lemmas of the form
   [coerce_* t eq_refl = t]. *)

Lemma JMeq_eq_refl {A} (x : A) : JMeq_eq (@JMeq_refl _ x) = eq_refl.
Proof. intros. apply proof_irrelevance. Qed.

Lemma UIP_refl_refl : forall A (x : A),
  Eqdep.EqdepTheory.UIP_refl A x eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Lemma inj_pairT2_refl : forall A (x : A) (P : A -> Type) (p : P x),
  Eqdep.EqdepTheory.inj_pairT2 A P x p p eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Polymorphic Lemma inj_sigma2_refl : forall A (x : A) (P : A -> Type) (p : P x),
  inj_sigma2 A P x p p eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Hint Rewrite @JMeq_eq_refl @UIP_refl_refl
     @inj_pairT2_refl : refl_id.
(** The inj_right_pair_refl lemma is now useful also when using noConfusion. *)
Hint Rewrite @inj_right_pair_refl : refl_id.
Hint Rewrite @HSets.inj_sigma_r_refl : refl_id.

Global Set Keyed Unification.

Ltac rewrite_sigma2_refl :=
  match goal with
    |- context [inj_sigma2 ?A ?P ?x ?p _ eq_refl] =>
    rewrite (inj_sigma2_refl A x P p)
   | |- context [@inj_right_sigma ?A ?H ?x ?P ?y ?y' _] =>
    rewrite (@inj_right_sigma_refl A H x P y)
   | |- context [@HSets.inj_sigma_r ?A ?H ?P ?x ?y ?y' _] =>
    rewrite (@HSets.inj_sigma_r_refl A H P x y)
  end.

Ltac rewrite_refl_id :=
  repeat (autorewrite with refl_id; try rewrite_sigma2_refl).

(** Clear the context and goal of equality proofs. *)

Ltac clear_eq_ctx :=
  rewrite_refl_id ; clear_eq_proofs.

(** Reapeated elimination of [eq_rect] applications.
   Abstracting equalities makes it run much faster than an naive implementation. *)

Ltac simpl_eqs :=
  repeat (elim_eq_rect ; simpl ; clear_eq_ctx).

(** Clear unused reflexivity proofs. *)

Ltac clear_refl_eq :=
  match goal with [ H : ?X = ?X |- _ ] => clear H end.
Ltac clear_refl_eqs := repeat clear_refl_eq.

(** Clear unused equality proofs. *)

Ltac clear_eq :=
  match goal with [ H : _ = _ |- _ ] => clear H end.
Ltac clear_eqs := repeat clear_eq.

(** Combine all the tactics to simplify goals containing coercions. *)

Ltac simplify_eqs :=
  simpl ; simpl_eqs ; clear_eq_ctx ; clear_refl_eqs ;
    try subst ; simpl ; repeat simpl_uip ; rewrite_refl_id.

(** A tactic that tries to remove trivial equality guards in induction hypotheses coming
   from [dependent induction]/[generalize_eqs] invocations. *)

Ltac simplify_IH_hyps := repeat
  match goal with
    | [ hyp : _ |- _ ] => specialize_eqs hyp
  end.

(** We split substitution tactics in the two directions depending on which 
   names we want to keep corresponding to the generalization performed by the
   [generalize_eqs] tactic. *)

Ltac subst_left_no_fail :=
  repeat (match goal with
            [ H : ?X = ?Y |- _ ] => subst X
          end).

Ltac subst_right_no_fail :=
  repeat (match goal with
            [ H : ?X = ?Y |- _ ] => subst Y
          end).

Ltac inject_left H :=
  progress (inversion H ; subst_left_no_fail ; clear_dups) ; clear H.

Ltac inject_right H :=
  progress (inversion H ; subst_right_no_fail ; clear_dups) ; clear H.

Ltac autoinjections_left := repeat autoinjection ltac:inject_left.
Ltac autoinjections_right := repeat autoinjection ltac:inject_right.

Ltac simpl_depind := subst_no_fail ; autoinjections ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

Ltac simpl_depind_l := subst_left_no_fail ; autoinjections_left ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

Ltac simpl_depind_r := subst_right_no_fail ; autoinjections_right ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

(** Support for the [Equations] command.
   These tactics implement the necessary machinery to solve goals produced by the
   [Equations] command relative to dependent pattern-matching.
   It is completely inspired from the "Eliminating Dependent Pattern-Matching" paper by
   Goguen, McBride and McKinna. *)


(** The NoConfusionPackage class provides a method for making progress on proving a property
   [P] implied by an equality on an inductive type [I]. The type of [noConfusion] for a given
   [P] should be of the form [ Π Δ, (x y : I Δ) (x = y) -> NoConfusion P x y ], where
   [NoConfusion P x y] for constructor-headed [x] and [y] will give a formula ending in [P].
   This gives a general method for simplifying by discrimination or injectivity of constructors.

   Some actual instances are defined later in the file using the more primitive [discriminate] and
   [injection] tactics on which we can always fall back.
   *)

Class NoConfusionPackage (A : Type) := {
  NoConfusion : A -> A -> Prop;
  noConfusion : forall a b, a = b -> NoConfusion a b
}.

(** Apply [noConfusion] on a given hypothsis. *)

Ltac noconf_ref H :=
  match type of H with
    @eq ?A ?X ?Y =>
      let H' := fresh in assert (H':=noConfusion (A:=A) X Y H) ;
      clear H; hnf in H'; 
      match type of H' with
      | True => clear H'
      | False => elim H'
      | @eq _ _ _ => revert dependent H'
      | _ => fail
      end
  end.

Ltac blocked t := block_goal ; t ; unblock_goal.

(** The [DependentEliminationPackage] provides the default dependent elimination principle to
   be used by the [equations] resolver. It is especially useful to register the dependent elimination
   principles for things in [Prop] which are not automatically generated. *)

Class DependentEliminationPackage (A : Type) :=
  { elim_type : Type ; elim : elim_type }.

(** A higher-order tactic to apply a registered eliminator. *)

Ltac elim_tac tac p :=
  let ty := type of p in
  let eliminator := eval simpl in (elim (A:=ty)) in
    tac p eliminator.

(** Specialization to do case analysis or induction.
   Note: the [equations] tactic tries [case] before [elim_case]: there is no need to register
   generated induction principles. *)

Ltac elim_case p := elim_tac ltac:(fun p el => destruct p using el) p.
Ltac elim_ind p := elim_tac ltac:(fun p el => induction p using el) p.

(** Lemmas used by the simplifier, mainly rephrasings of [eq_rect], [eq_ind]. *)

Lemma solution_left : ∀ {A} {B : A -> Type} (t : A), B t -> (∀ x, x = t -> B x).
Proof. intros A B t H x eq. destruct eq. apply H. Defined.

Polymorphic
Lemma Id_solution_left : ∀ {A} {B : A -> Type} (t : A), B t -> (∀ x, Id x t -> B x).
Proof. intros A B t H x eq. destruct eq. apply H. Defined.

Scheme eq_rect_dep := Induction for eq Sort Type.

Lemma eq_rect_dep_r {A} (x : A) (P : forall a, a = x -> Type) (p : P x eq_refl)
      (y : A) (e : y = x) : P y e.
Proof. destruct e. apply p. Defined.

Polymorphic
Lemma Id_rect_dep_r {A} (x : A) (P : forall a, Id a x -> Type) (p : P x id_refl)
      (y : A) (e : Id y x) : P y e.
Proof. destruct e. apply p. Defined.

Lemma solution_left_dep : ∀ {A} (t : A) {B : forall (x : A), (x = t -> Type)},
    B t eq_refl -> (∀ x (Heq : x = t), B x Heq).
Proof. intros A t B H x eq. destruct eq. apply H. Defined.

Polymorphic
Lemma Id_solution_left_dep : ∀ {A} (t : A) {B : forall (x : A), (Id x t -> Type)},
    B t id_refl -> (∀ x (Heq : Id x t), B x Heq).
Proof. intros A t B H x eq. destruct eq. apply H. Defined.

Lemma solution_right : ∀ {A} {B : A -> Type} (t : A), B t -> (∀ x, t = x -> B x).
Proof. intros A B t H x eq. destruct eq. apply H. Defined.

Polymorphic
Lemma Id_solution_right : ∀ {A} {B : A -> Type} (t : A), B t -> (∀ x, Id t x -> B x).
Proof. intros A B t H x eq. destruct eq. apply H. Defined.

Lemma solution_right_dep : ∀ {A} (t : A) {B : forall (x : A), (t = x -> Type)},
    B t eq_refl -> (∀ x (Heq : t = x), B x Heq).
Proof. intros A t B H x eq. destruct eq. apply H. Defined.

Polymorphic
Lemma Id_solution_right_dep : ∀ {A} (t : A) {B : forall (x : A), (Id t x -> Type)},
    B t id_refl -> (∀ x (Heq : Id t x), B x Heq).
Proof. intros A t B H x eq. destruct eq. apply H. Defined.

Lemma solution_left_let : ∀ {A} {B : A -> Type} (b : A) (t : A), 
  (b = t -> B t) -> (let x := b in x = t -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Lemma solution_right_let : ∀ {A} {B : A -> Type} (b t : A), 
  (t = b -> B t) -> (let x := b in t = x -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Polymorphic
Lemma Id_solution_left_let : ∀ {A} {B : A -> Type} (b : A) (t : A), 
  (Id b t -> B t) -> (let x := b in Id x t -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Polymorphic
Lemma Id_solution_right_let : ∀ {A} {B : A -> Type} (b t : A), 
  (Id t b -> B t) -> (let x := b in Id t x -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Lemma deletion : ∀ {A B} (t : A), B -> (t = t -> B).
Proof. intros; assumption. Defined.

Polymorphic
Lemma Id_deletion : ∀ {A B} (t : A), B -> (Id t t -> B).
Proof. intros; assumption. Defined.

Lemma simplification_heq : ∀ {A B} (x y : A), (x = y -> B) -> (JMeq x y -> B).
Proof. intros; apply X; apply (JMeq_eq H). Defined.

Lemma simplification_existT2 : ∀ {A} {P : A -> Type} {B} (p : A) (x y : P p),
  (x = y -> B) -> (existT P p x = existT P p y -> B).
Proof. intros. apply X. apply inj_pair2. exact H. Defined.

Polymorphic Lemma simplification_sigma2 : ∀ {A} {P : A -> Type} {B} (p : A) (x y : P p),
  (x = y -> B) -> (sigmaI P p x = sigmaI P p y -> B).
Proof. intros. apply X. apply inj_sigma2. exact H. Defined.

(** If we have decidable equality on [A] we use this version which is 
   axiom-free! *)

Lemma simplification_existT2_dec : ∀ {A} `{EqDec A} {P : A -> Type} {B} (p : A) (x y : P p),
  (x = y -> B) -> (existT P p x = existT P p y -> B).
Proof. intros. apply X. apply inj_right_pair in H0. assumption. Defined.

Polymorphic Lemma simplification_sigma2_dec : ∀ {A} `{EqDec A} {P : A -> Type} {B}
    (p : A) (x y : P p),
    (x = y -> B) -> (sigmaI P p x = sigmaI P p y -> B).
Proof. intros. apply X. apply inj_right_sigma in H0. assumption. Defined.

Polymorphic Lemma simplification_sigma2_cst : ∀ {A} {P : Type} {B} (p : A) (x y : P),
  (x = y -> B) -> (sigmaI (fun _ => P) p x = sigmaI (fun _ => P) p y -> B).
Proof. intros. apply X. change (x = pr2 (sigmaI _ p y)). destruct H. reflexivity. Defined.

Polymorphic Lemma Id_simplification_sigma2 : ∀ {A} `{HSets.HSet A} {P : A -> Type} {B}
                                               (p : A) (x y : P p),
  (Id x y -> B) -> (Id (sigmaI P p x) (sigmaI P p y) -> B).
Proof. intros. apply X. apply HSets.inj_sigma_r. exact X0. Defined.

Lemma simplification_existT1 : ∀ {A} {P : A -> Type} {B} (p q : A) (x : P p) (y : P q),
  (p = q -> existT P p x = existT P q y -> B) -> (existT P p x = existT P q y -> B).
Proof. intros. injection H. intros ; auto. Defined.

Polymorphic Lemma simplification_sigma1 : ∀ {A} {P : A -> Type} {B} (p q : A) (x : P p) (y : P q),
  (p = q -> sigmaI P p x = sigmaI P q y -> B) -> (sigmaI P p x = sigmaI P q y -> B).
Proof.
  intros. refine (X _ H).
  change (pr1 (p; x) = pr1 (q; y)).
  now destruct H.
Defined.

Polymorphic Lemma Id_simplification_sigma1 {A} {P : A -> Type} {B} (p q : A) (x : P p) (y : P q) :
  (Id p q -> Id (sigmaI P p x) (sigmaI P q y) -> B) -> (Id (sigmaI P p x) (sigmaI P q y) -> B).
Proof.
  intros. refine (X _ X0).
  change (Id (pr1 (p; x)) (pr1 (q; y))).
  now destruct X0.
Defined.

Lemma simplification_K : ∀ {A} (x : A) {B : x = x -> Type}, B eq_refl -> (∀ p : x = x, B p).
Proof. intros. rewrite (UIP_refl A). assumption. Defined.

Lemma simplification_K_dec : ∀ {A} `{EqDec A} (x : A) {B : x = x -> Type}, 
  B eq_refl -> (∀ p : x = x, B p).
Proof. intros. apply K_dec. assumption. Defined.

Polymorphic
Lemma Id_simplification_K : ∀ {A} `{HSets.HSet A} (x : A) {B : Id x x -> Type}, 
  B id_refl -> (∀ p : Id x x, B p).
Proof. intros. apply HSets.K. assumption. Defined.

(** This hint database and the following tactic can be used with [autounfold] to 
   unfold everything to [eq_rect]s. *)

Hint Unfold solution_left solution_right deletion simplification_heq
  simplification_existT1 simplification_existT2 simplification_K
  simplification_sigma1 simplification_sigma2 simplification_sigma2_dec
  simplification_K_dec simplification_existT2_dec
  Id_solution_left Id_solution_right Id_deletion
  Id_solution_left_dep Id_solution_right_dep Id_solution_right_let Id_solution_left_let
  Id_simplification_sigma1 Id_simplification_sigma2 Id_simplification_K  
  eq_rect_r eq_rec eq_ind : equations.

(** Makes these definitions disappear at extraction time *)
Extraction Inline solution_right_dep solution_right solution_left solution_left_dep.
Extraction Inline solution_right_let solution_left_let deletion.
Extraction Inline simplification_heq simplification_existT2.
Extraction Inline simplification_existT1 simplification_existT2_dec.
Extraction Inline simplification_sigma1 simplification_sigma2_dec.
Extraction Inline simplification_sigma2.
Extraction Inline simplification_K simplification_K_dec.
Extraction Inline Id_solution_right_dep Id_solution_right Id_solution_left Id_solution_left_dep.
Extraction Inline Id_solution_right_let Id_solution_left_let Id_deletion.
Extraction Inline Id_simplification_sigma1 Id_simplification_sigma2 Id_simplification_K.

(** Simply unfold as much as possible. *)

Ltac unfold_equations := repeat progress autounfold with equations.
Ltac unfold_equations_in H := repeat progress autounfold with equations in H.

(** The tactic [simplify_equations] is to be used when a program generated using [Equations] 
   is in the goal. It simplifies it as much as possible, possibly using [K] if needed.
   The argument is the concerned equation. *) 

Ltac simplify_equations f := repeat ((unfold_equations ; simplify_eqs ; 
  try autounfoldify f) || autorewrite with equations). 

Ltac simplify_equations_in e :=
  repeat progress (autounfold with equations in e ; simpl in e).

(** Using these we can make a simplifier that will perform the unification
   steps needed to put the goal in normalised form (provided there are only
   constructor forms). Compare with the lemma 16 of the paper.
   We don't have a [noCycle] procedure yet. *)

Ltac block_equality id :=
  match type of id with
    | @eq ?A ?t ?u => change (let _ := block in (@eq A t u)) in id
    | _ => idtac
  end.

Ltac revert_blocking_until id := 
  Tactics.on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => block_equality id' ; revert id' ; revert_blocking_until id
    end).

Ltac simplify_one_dep_elim_term c :=
  match c with
    | @JMeq _ _ _ _ -> _ => refine (@simplification_heq _ _ _ _ _)
    | ?t = ?t -> _ => intros _ || apply simplification_K_dec || refine (@simplification_K _ t _ _)
    | Id ?t ?t -> _ => intros _ || apply Id_simplification_K
    | (@existT ?A ?P ?n ?x) = (@existT ?A ?P ?m ?y) -> ?B =>
      (* Check if [n] and [m] are judgmentally equal. *)
      match goal with
      | |- _ =>
        try (try (refine (@simplification_existT2 _ _ _ _ _ _ _); []; gfail 1); fail 1);
        match goal with
        | _ : x = y |- _ => intro
        | _ =>
          apply (simplification_existT2_dec (A:=A) (P:=P) (B:=B) n x y) ||
            refine (@simplification_existT2 _ _ _ _ _ _ _)
        end
      | |- _ =>
        match goal with
        | _ : n = m |- _ => intro
        | _ => refine (@simplification_existT1 _ _ _ _ _ _ _ _)
        end
      end
    | (@sigmaI ?A ?P ?n ?x) = (@sigmaI _ _ ?m ?y) -> ?B =>
      (* Check if [n] and [m] are judgmentally equal. *)
      match goal with
      | |- _ =>
        try (try (refine (@simplification_sigma2 _ _ _ _ _ _ _); []; gfail 1); fail 1);
        match goal with
        | _ : x = y |- _ => intro
        | _ =>
          apply (simplification_sigma2_dec (A:=A) (P:=P) (B:=B) n x y) ||
            refine (@simplification_sigma2 _ _ _ _ _ _ _)
        end
      | |- _ =>
        match goal with
        | _ : n = m |- _ => intro
        | _ => refine (@simplification_sigma1 _ _ _ _ _ _ _ _)
        end
      end

    | Id (@sigmaI ?A ?P ?n ?x) (@sigmaI _ _ ?m ?y) -> ?B =>
      (* Check if [n] and [m] are judgmentally equal. *)
      match goal with
      | |- _ => unify n m;
        match goal with
        | _ : Id x y |- _ => intro
        | _ =>
          apply (Id_simplification_sigma2 (A:=A) (P:=P) (B:=B) n x y) ||
                fail 100000 "Type " A " is not a declared HSet: cannot simplify"
        end
      | |- _ =>
        match goal with
        | _ : Id n m |- _ => intro
        | _ => refine (@Id_simplification_sigma1 _ _ _ _ _ _ _ _)
        end
      end

    | forall H : ?x = ?y, _ => (* variables case *)
      (let hyp := fresh H in intros hyp ;
        move hyp before x ; move x before hyp; revert_blocking_until x; revert x;
          (match goal with
            | |- let x := _ in _ = _ -> @?B x =>
               refine (@solution_left_let _ B _ _ _)
             | _ => refine (@solution_left _ _ _ _) || refine (@solution_left_dep _ _ _ _)
           end)) ||
      (let hyp := fresh "Heq" in intros hyp ;
        move hyp before y ; move y before hyp; revert_blocking_until y; revert y;
          (match goal with
             | |- let x := ?b in (let _ := block in ?t = _) -> @?B x =>
               (refine (@solution_right_let _ B _ _ _); let B' := eval cbv beta in (B t) in
                                                            change (t = b -> B'))
             | _ => refine (@solution_right _ _ _ _) || refine (@solution_right_dep _ _ _ _)
           end))

    | forall H : Id ?x ?y, _ => (* variables case *)
      (let hyp := fresh H in intros hyp ;
        move hyp before x ; move x before hyp; revert_blocking_until x; revert x;
          (match goal with
            | |- let x := _ in Id _ _ -> @?B x =>
               refine (@Id_solution_left_let _ B _ _ _)
             | _ => refine (@Id_solution_left _ _ _ _) || refine (@Id_solution_left_dep _ _ _ _)
           end)) ||
      (let hyp := fresh "Heq" in intros hyp ;
        move hyp before y ; move y before hyp; revert_blocking_until y; revert y;
          (match goal with
             | |- let x := ?b in (let _ := block in Id ?t _) -> @?B x =>
               (refine (@Id_solution_right_let _ B _ _ _); let B' := eval cbv beta in (B t) in
                                                            change (t = b -> B'))
             | _ => refine (@Id_solution_right _ _ _ _) || refine (@Id_solution_right_dep _ _ _ _)
           end))

    | @eq ?A ?t ?u -> ?P => let hyp := fresh in intros hyp ; noconf_ref hyp

    | @Id ?A ?t ?u -> ?P => let hyp := fresh in intros hyp ; noconf_ref hyp

    | ?f ?x = ?g ?y -> _ => let H := fresh in progress (intros H ; injection H ; clear H)

    | Id (?f ?x) (?g ?y) -> _ => let H := fresh in progress (intros H ; inversion H ; clear H)

    | ?t = ?u -> _ => let hyp := fresh in
      intros hyp ; elimtype False ; discriminate

    | Id ?t ?u -> _ => let hyp := fresh in
      intros hyp ; elimtype False ; solve [inversion hyp]

    | ?x = ?y -> _ => let hyp := fresh in
      intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
        case hyp (* ; clear hyp *)

    | Id _ ?x ?y -> _ => let hyp := fresh in
      intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
        case hyp (* ; clear hyp *)

    | let _ := block in _ => fail 1 (* Do not put any part of the rhs in the hyps *)
    | _ -> ?B => let ty := type of B in (* Works only with non-dependent products *)
      intro || (let H := fresh in intro H)
    | forall x, _ =>
      let H := fresh x in intro H
    | _ => intro

    (* | _ -> ?T => intro; try (let x := type of T in idtac) *)
    (*    (* Only really anonymous, non dependent hyps get automatically generated names. *) *)
    (* | forall x, _ => intro x || (let H := fresh x in rename x into H ; intro x) (* Try to keep original names *) *)
    (* | _ -> _ => intro *)
  end.

Ltac simplify_one_dep_elim :=
  match goal with
    | [ |- context [eq_rect_r _ _ eq_refl]] => unfold eq_rect_r at 1; simpl eq_rect
    | [ |- context [@eq_rect_dep_r _ _ _ _ _ eq_refl]] => simpl eq_rect_dep_r
    | [ |- context [@Id_rect_dep_r _ _ _ _ _ id_refl]] => simpl Id_rect_dep_r
    | [ |- ?gl ] => simplify_one_dep_elim_term gl
  end.

(** Repeat until no progress is possible. By construction, it should leave the goal with
   no remaining equalities generated by the [generalize_eqs] tactic. *)

Ltac simplify_dep_elim := repeat simplify_one_dep_elim.

Ltac noconf H ::= blocked ltac:(noconf_ref H ; simplify_dep_elim).

(** Reverse and simplify. *)

Ltac simpdep := reverse; simplify_dep_elim.

(** The default implementation of generalization using JMeq. *)

Ltac generalize_by_eqs id := generalize_eqs id.
Ltac generalize_by_eqs_vars id := generalize_eqs_vars id.

(** Do dependent elimination of the last hypothesis, but not simplifying yet
   (used internally). *)

Ltac destruct_last :=
  on_last_hyp ltac:(fun id => simpl in id ; generalize_by_eqs id ; destruct id).

(** The rest is support tactics for the [Equations] command. *)

(** Notation for inaccessible patterns. *)

Definition inaccessible_pattern {A : Type} (t : A) := t.

Notation "?( t )" := (inaccessible_pattern t).

Definition hide_pattern {A : Type} (t : A) := t.

Definition add_pattern {B} (A : Type) (b : B) := A.

(** To handle sections, we need to separate the context in two parts:
   variables introduced by the section and the rest. We introduce a dummy variable
   between them to indicate that. *)

CoInductive end_of_section := the_end_of_the_section.

Ltac set_eos := let eos := fresh "eos" in
  assert (eos:=the_end_of_the_section).

Ltac with_eos_aux tac :=
  match goal with
   [ H : end_of_section |- _ ] => tac H
  end.

Ltac with_eos tac orelse :=
  with_eos_aux tac + (* No section variables *) orelse.

Ltac clear_nonsection :=
  repeat match goal with
    [ H : ?T |- _ ] =>
    match T with
      end_of_section => idtac
    | _ => clear H
    end
  end.

(** We have a specialized [reverse_local] tactic to reverse the goal until the begining of the
   section variables *)

Ltac reverse_local :=
  match goal with
    | [ H : ?T |- _ ] =>
      match T with
        | end_of_section => idtac
        | _ => revert H ; reverse_local 
      end
    | _ => idtac
  end.

Ltac clear_local :=
  match goal with
    | [ H : ?T |- _ ] =>
      match T with
        | end_of_section => idtac
        | _ => clear H ; clear_local 
      end
    | _ => idtac
  end.

(** Do as much as possible to apply a method, trying to get the arguments right.
   !!Unsafe!! We use [auto] for the [_nocomp] variant of [Equations], in which case some
   non-dependent arguments of the method can remain after [apply]. *)

Ltac simpl_intros m := ((apply m || refine m) ; auto) || (intro ; simpl_intros m).

(** Hopefully the first branch suffices. *)

Ltac try_intros m :=
  solve [ (intros_until_block ; refine m || (unfold block ; apply m)) ; auto ] ||
  solve [ unfold block ; simpl_intros m ] ||
  solve [ unfold block ; intros ; rapply m ; eauto ].

(** To solve a goal by inversion on a particular target. *)

Ltac do_empty id :=
  elimtype False ; simpl in id ;
  solve [ generalize_by_eqs id ; destruct id ; simplify_dep_elim
    | apply id ; eauto with Below ].

Ltac solve_empty target :=
  do_nat target intro ; on_last_hyp ltac:do_empty.

Ltac simplify_method tac := repeat (tac || simplify_one_dep_elim) ; reverse_local.

Ltac clear_fix_protos n tac :=
  match goal with
    | [ |- (let _ := fixproto in _) -> _ ] => intros _ ; 
      match n with
        | O => fail 2 "clear_fix_proto: tactic would apply on prototype"
        | S ?n => clear_fix_protos n tac
      end
    | [ |- let _ := block in _ ] => reverse_local ; tac n
    | _ => reverse_local ; tac n
  end.

(** Solving a method call: we can solve it by splitting on an empty family member
   or we must refine the goal until the body can be applied. *)

Ltac solve_method rec :=
  match goal with
    | [ H := ?body : nat |- _ ] => subst H ; clear ; clear_fix_protos body
      ltac:(fun n => abstract (simplify_method idtac ; solve_empty n))
    | [ H := ?body : ?T |- _ ] => clear H ; simplify_method ltac:(exact body) ; rec ; 
      try (exact (body : T)) ; try_intros (body:T)
  end.

(** Impossible cases, by splitting on a given target. *)

Ltac solve_split :=
  match goal with 
    | [ |- let split := ?x : nat in _ ] => intros _ ;
      clear_fix_protos x ltac:(fun n => clear ; abstract (solve_empty n))
  end.

(** If defining recursive functions, the prototypes come first. *)

Ltac intro_prototypes :=
  match goal with
    | [ |- ∀ x : _, _ ] => intro ; intro_prototypes
    | _ => idtac
  end.

Ltac introduce p := first [
  match p with _ => (* Already there, generalize dependent hyps *)
    generalize dependent p ; intros p
  end
  | intros until p | intros until 1 | intros ].

Ltac do_case p := introduce p ; (elim_case p || destruct p || (case p ; clear p)).
Ltac do_ind p := introduce p ; (elim_ind p || induction p).

Ltac case_last := block_goal ;
  on_last_hyp ltac:(fun p => 
    let ty := type of p in
      match ty with
        | ?x = ?x => revert p ; refine (simplification_K _ x _ _)
        | ?x = ?y => revert p
        | _ => simpl in p ; try simplify_equations_in p ; generalize_by_eqs p ; do_case p
      end).

Ltac nonrec_equations :=
  solve [solve_equations (case_last) (solve_method idtac)] || solve [ solve_split ]
    || fail "Unnexpected equations goal".

Ltac recursive_equations :=
  solve [solve_equations (case_last) (solve_method ltac:intro)] || solve [ solve_split ]
    || fail "Unnexpected recursive equations goal".

(** The [equations] tactic is the toplevel tactic for solving goals generated
   by [Equations]. *)

Ltac equations := set_eos ;
  (*match goal with |- ?gl => idtac gl end;*)
  match goal with
    | [ |- ∀ x : _, _ ] => intro ; recursive_equations
    | [ |- let x := _ in ?T ] => intro x ; exact x
    | _ => nonrec_equations
  end.

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

(** The [do_depelim] higher-order tactic takes an elimination tactic as argument and an hypothesis 
   and starts a dependent elimination using this tactic. *)

Ltac is_introduced H :=
  match goal with
    | [ H' : _ |- _ ] => match H' with H => idtac end
  end.

Tactic Notation "intro_block" hyp(H) :=
  (is_introduced H ; block_goal ; revert_until H ; block_goal) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Tactic Notation "intro_block_id" ident(H) :=
  (is_introduced H ; block_goal ; revert_until H ; block_goal) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Ltac unblock_dep_elim :=
  match goal with
    | |- let _ := block in ?T => 
      match T with context [ block ] => 
        change T ; intros_until_block
      end
    | _ => unblock_goal
  end.

Ltac simpl_dep_elim := simplify_dep_elim ; simplify_IH_hyps ; unblock_dep_elim.

Ltac do_intros H :=
  (try intros until H) ; (intro_block_id H || intro_block H) ;
  (try simpl in H ; simplify_equations_in H).

Ltac do_depelim_nosimpl tac H := do_intros H ; generalize_by_eqs H ; tac H.

Ltac do_depelim tac H := do_depelim_nosimpl tac H ; simpl_dep_elim; unblock_goal.

Ltac do_depind tac H := 
  (try intros until H) ; intro_block H ; (try simpl in H ; simplify_equations_in H) ;
  generalize_by_eqs_vars H ; tac H ; simpl_dep_elim; unblock_goal.

(** To dependent elimination on some hyp. *)

Ltac depelim id := do_depelim ltac:(fun hyp => do_case hyp) id.

Ltac depelim_term c :=
  let H := fresh "term" in
    set (H:=c) in *; clearbody H ; depelim H.

(** Used internally. *)

Ltac depelim_nosimpl id := do_depelim_nosimpl ltac:(fun hyp => do_case hyp) id.

(** To dependent induction on some hyp. *)

Ltac depind id := do_depind ltac:(fun hyp => do_ind hyp) id.

(** A variant where generalized variables should be given by the user. *)

Ltac do_depelim' tac H :=
  (try intros until H) ; block_goal ; generalize_by_eqs H ; tac H ; simplify_dep_elim ; 
    simplify_IH_hyps ; unblock_goal.

(** Calls [destruct] on the generalized hypothesis, results should be similar to inversion.
   By default, we don't try to generalize the hyp by its variable indices.  *)

Tactic Notation "dependent" "destruction" ident(H) := 
  do_depelim' ltac:(fun hyp => do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => destruct hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the elimination. *)

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => revert l ; do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => revert l ; destruct hyp using c) H.

(** Then we have wrappers for usual calls to induction. One can customize the induction tactic by 
   writting another wrapper calling do_depelim. We suppose the hyp has to be generalized before
   calling [induction]. *)

Tactic Notation "dependent" "induction" ident(H) :=
  do_depind ltac:(fun hyp => do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "using" constr(c) :=
  do_depind ltac:(fun hyp => induction hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; induction hyp using c) H.

(** For treating impossible cases. Equations corresponding to impossible
   calls form instances of [ImpossibleCall (f args)]. *)

Class ImpossibleCall {A : Type} (a : A) : Type :=
  is_impossible_call : False.

(** We have a trivial elimination operator for impossible calls. *)

Definition elim_impossible_call {A} (a : A) {imp : ImpossibleCall a} (P : A -> Type) : P a :=
  match is_impossible_call with end.

(** The tactic tries to find a call of [f] and eliminate it. *)

Ltac impossible_call f := on_call f ltac:(fun t => apply (elim_impossible_call t)).

(** [solve_equation] is used to prove the equation lemmas for an existing definition.  *)

Ltac find_empty := simpl in * ; elimtype False ;
  match goal with
    | [ H : _ |- _ ] => solve [ clear_except H ; depelim H | specialize_eqs H ; assumption ]
    | [ H : _ <> _ |- _ ] => solve [ red in H ; specialize_eqs H ; assumption ]
  end.

Ltac make_simplify_goal :=
  match goal with 
    [ |- @eq ?A ?T ?U ] => let eqP := fresh "eqP" in 
      set (eqP := fun x : A => x = U) ; change (eqP T)
  | [ |- @Id ?A ?T ?U ] => let eqP := fresh "eqP" in 
      set (eqP := fun x : A => @Id A x U) ; change (eqP T)
  end.

Ltac hnf_gl :=
  match goal with 
    [ |- ?P ?T ] => let T' := eval hnf in T in
      convert_concl_no_check (P T')
  end.

Ltac hnf_eq :=
  match goal with
    |- ?x = ?y =>
      let x' := eval hnf in x in
      let y' := eval hnf in y in
        convert_concl_no_check (x' = y')
  | |- Id ?x ?y =>
    let x' := eval hnf in x in
    let y' := eval hnf in y in
        convert_concl_no_check (Id x' y')
  end.

Ltac simpl_equations :=
  repeat (hnf_eq ; unfold_equations; rewrite_refl_id).

Ltac simpl_equation_impl :=
  repeat (unfold_equations; rewrite_refl_id).

Ltac simplify_equation := 
  make_simplify_goal ; repeat (hnf_gl ; simpl; unfold_equations; rewrite_refl_id).

Ltac solve_equation := 
  intros ; try simplify_equation ; try
    (match goal with 
       | [ |- ImpossibleCall _ ] => elimtype False ; find_empty 
       | _ => reflexivity || discriminates
     end).
