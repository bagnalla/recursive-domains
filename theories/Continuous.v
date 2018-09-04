Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Le.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Coq.Program.Equality.

Require Import Domains.Domain Domains.Order.

(* It would be nice to only require a proof of continuity and show
   that continuity implies properness (monotonicity), but the way it
   is defined here requires knowing properness to express continuity
   :/. *)

(* The type of continuous functions between ordered types. We require
   supremum instances for both types in order to cleanly express
   continuity. *)
Record CFun A B `{RA : Supremum A} `{RB : Supremum B} :=
  { cfun_app : A -> B
  ; cfun_Proper : Proper (oleq ==> oleq) cfun_app
  ; cfun_Continuous : forall A,
      cfun_app (supremum A) =o= supremum (omegaChainMap cfun_app cfun_Proper A)
  }.

Arguments cfun_app {_ _ _ _ _ _}.
Arguments cfun_Proper {_ _ _ _ _ _}.

Notation "A '-c>' B" := (CFun A B) (right associativity, at level 99).
Notation "x @c@ y" := (cfun_app x y) (left associativity, at level 20).


(* Ordering on continuous function spaces. *)
Program Instance OTcarrow A B `{supA : Supremum A} `{supB : Supremum B}
  : OType (A -c> B) :=
  {| oleq :=
       fun f g =>
         forall a1 a2, oleq a1 a2 ->
                  oleq (f @c@ a1) (g @c@ a2) |}.
Next Obligation.
  constructor.
  - intros ? ? ? ?; apply cfun_Proper; assumption.
  - intros ? g ? H0 H1 x y Hleq; specialize (H0 x y Hleq).
    transitivity (g @c@ y); auto.
    apply H1; firstorder.
Defined.

(* Pointwise application of an ω-chain of functions to a fixed
   argument, yielding an ω-chain of codomain values. *)
Program Definition apply_chain {A B : Type} `{supA : Supremum A}
        `{supB : Supremum B} (ch : @omegaChain (A -c> B) _) (x : A)
  : @omegaChain B _ :=
  fun n => cfun_app (ch n) x.
Next Obligation.
  intros j; destruct ch as [ch ax]; apply ax; reflexivity.
Qed.

(* apply_chain is monotone. *)
Instance Proper_apply_chain {A B : Type} `{supA : Supremum A}
         `{supB : Supremum B} (G : @omegaChain (A -c> B) _) :
  Proper (oleq ==> oleq) (apply_chain G).
Proof.
  intros x y Hleq n; destruct G; simpl;
    destruct x0; simpl; rewrite Hleq; reflexivity.
Qed.

(* Supremum and CPO instances for continuous function spaces. Not the
   most beautiful proofs.. *)
Program Instance ContinuousHomSupremum
        {A B} {oA : OType A} {oB : OType B}
         (supA : @Supremum A oA) (supB : @Supremum B oB)
         {cpoA : CPO A} {cpoB : CPO B}
  : @Supremum (A -c> B) (OTcarrow _ _) :=
  fun ch => {| cfun_app := fun x => supB (apply_chain ch x) |}.
Next Obligation.
  intros ? ? Hleq; destruct cpoB;
    apply supremumProper; rewrite Hleq; reflexivity.
Qed.
Next Obligation.
  unfold supremum, apply_chain, omegaChainMap; destruct cpoB.
  destruct ch; simpl.
  rename A0 into G.
  destruct ((exist (fun g : nat -> B => omegaAx B g) (fun n : nat => x n @c@ supA G)
                   (apply_chain_obligation_1 A B oA supA oB supB
          (exist (fun g : nat -> A -c> B => omegaAx (A -c> B) g) x o)
          (supA G)))) eqn:HG1.
  inversion HG1.
  assert ((fun n => x n @c@ supA G) =o=
          fun n => supB (omegaChainMap (cfun_app (x n))
                                    (cfun_Proper (x n)) G)).
  { split; simpl.
    - intros n. destruct (x n). simpl.
      apply cfun_Continuous0.
    - intros n. destruct (x n). simpl.
      apply cfun_Continuous0. }
  assert (Hax:
            omegaAx B ((fun n : nat =>
                          supB (omegaChainMap (cfun_app (x n))
                                              (cfun_Proper (x n)) G)))).
  { intros j; destruct H; subst.
    pose proof o0 as H0; specialize (H0 j).
    simpl in *; specialize (H (S j)); specialize (H1 j).
    etransitivity. apply H1. etransitivity. apply H0. apply H. }
  assert (Hex: exist (fun g : nat -> B => omegaAx B g) x0 o0 =o=
               exist (fun g : nat -> B => omegaAx B g)
                     ((fun n : nat =>
                         supB (omegaChainMap (cfun_app (x n))
                                             (cfun_Proper (x n)) G)))
                     Hax).
  { split; simpl; intros n; destruct H; simpl in *;
      specialize (H n); subst; try apply H; apply H1. }
  etransitivity.
  apply Proper_oleq_oeq. apply Hex. unfold omegaChainMap. simpl.
  split; simpl.
  + edestruct supremumAx; apply H2; intros j; simpl.
    destruct ((exist (fun g : nat -> B => omegaAx B g)
                     (fun n : nat => supB (omegaChainMap
                                        (cfun_app (x n))
                                        (cfun_Proper (x n)) G)) Hax))
             eqn:HG2. inversion HG2.
    edestruct supremumAx; apply H5; intros i; destruct G.
    edestruct supremumAx; specialize (H6 i); etransitivity.
    shelve. apply H6. Unshelve.
    edestruct supremumAx; specialize (H1 j); etransitivity.
    shelve. apply H8. Unshelve.
    simpl; reflexivity.
  + edestruct supremumAx; apply H2; intros j; simpl.
    destruct ((exist (fun g : nat -> B => omegaAx B g)
                     (fun n : nat => supB (omegaChainMap
                                        (cfun_app (x n))
                                        (cfun_Proper (x n)) G)) Hax))
             eqn:HG2. inversion HG2.
    edestruct supremumAx; apply H5; intros i; destruct G.
    edestruct supremumAx; specialize (H6 i); etransitivity.
    shelve. apply H6. Unshelve.
    edestruct supremumAx; specialize (H1 j); etransitivity.
    shelve. apply H8. Unshelve.
    simpl; reflexivity.
Qed.

Instance ContinuousHomCPO {A B} `(cpoA : CPO A) `(cpoB : CPO B)
  : CPO (A -c> B).
Proof.
  constructor.
  - intros G. split.
    + intros j x y Hleq; destruct cpoB.
      destruct (supremumAx (apply_chain G y)).
      specialize (H j); destruct G; simpl in *.
      etransitivity. shelve. apply H. Unshelve.
      destruct (x0 j); simpl; rewrite Hleq; reflexivity.
    + intros b Hub x y Hleq; destruct cpoB.
      destruct (supremumAx (apply_chain G y)).
      etransitivity. shelve.
      apply H0; intros j; specialize (Hub j).
      destruct G; apply Hub; reflexivity.
      Unshelve.
      apply supremumProper; intros n; destruct G;
        simpl; destruct (x0 n); firstorder.
  - intros x y Hleq1 a b Hleq2.
    destruct cpoB; apply supremumProper; intros n; destruct x, y.
    etransitivity. apply Hleq1. apply Hleq2. reflexivity.
Qed.


(** Some standard continuous functions constructions. *)

(* The identity continuous function. *)
Program Definition id_cfun A `{CPO A} : A -c> A :=
  {| cfun_app := fun x => x; cfun_Proper := fun x1 x2 Rx => Rx |}.
Next Obligation.
  destruct H; apply Proper_oleq_oeq.
  rewrite omegaChainMap_id; reflexivity.
Qed.

(* A continuous function that returns the constant b. *)
Program Definition const_cfun {A B} `{Supremum A} `{CPO B} (b : B)
  : A -c> B := {| cfun_app := fun _ => b |}.
Next Obligation. intros ?; reflexivity. Qed.
Next Obligation.
  destruct H0 as [ax _].
  specialize (ax (omegaChainMap
                    (fun _ => b) (const_cfun_obligation_1 _ _ _ _ _) A0)).
  destruct ax; specialize (H0 0).
  assert (H2: upper_bound b (omegaChainMap
                               (fun _ : A => b)
                               (const_cfun_obligation_1 A B o o0 b) A0)).
  { intros j; reflexivity. }
  firstorder.
Qed.

(* Tupling of continuous functions. *)
Program Definition tuple_cfun {A B C} `{CPO A} `{CPO B} `{CPO C}
        (f : A -c> B) (g : A -c> C) : A -c> (B*C) :=
  {| cfun_app := fun x => (cfun_app f x, cfun_app g x) |}.
Next Obligation.
  intros x y Hleq; destruct f, g; simpl; split.
  - apply cfun_Proper0; auto.
  - apply cfun_Proper1; auto.
Qed.
Next Obligation.
  destruct f as [f Hfprop Hfcont], g as [g Hgprop Hgcont].
  rewrite Hfcont, Hgcont; destruct H0 as [? supProp1], H1 as [? supProp2].
  split; split; try apply supProp1; try apply supProp2;
    intros n; destruct A0; simpl; reflexivity.
Qed.

(* Pairing of continuous functions. Technically redundant but
   sometimes convenient. *)
Program Definition pair_cfun {A B C D} `{CPO A} `{CPO B} `{CPO C}
        `{CPO D} (f : A -c> C) (g : B -c> D) : (A*B) -c> (C*D) :=
  {| cfun_app := fun p => let (x, y) := p in
                       (cfun_app f x, cfun_app g y) |}.
Next Obligation.
  intros [a1 b1] [a2 b2] [Hleq1 Hleq2]; simpl.
  destruct f, g; auto.
Qed.
Next Obligation.
  destruct f as [f Hfprop Hfcont], g as [g Hgprop Hgcont].
  rewrite Hfcont, Hgcont; destruct H1 as [? supProp1], H2 as [? supProp2].
  split; split; try apply supProp1; try apply supProp2;
    intros n; destruct A0; simpl; destruct (x n); reflexivity.
Qed.

(* Continuous first projection function. *)
Program Definition fst_cfun {A B} `{CPO A} `{CPO B} : (A*B) -c> A :=
  {| cfun_app := fun p => fst p |}.
Next Obligation. firstorder. Qed.
Next Obligation.
  destruct H as [? ?]; apply Proper_oleq_oeq;
    split; intros n; reflexivity.
Qed.

(* Continuous second projection function. *)
Program Definition snd_cfun {A B} `{CPO A} `{CPO B} : (A*B) -c> B :=
  {| cfun_app := fun p => snd p |}.
Next Obligation. firstorder. Qed.
Next Obligation.
  destruct H0 as [? ?]; apply Proper_oleq_oeq;
    split; intros n; reflexivity.
Qed.

(* Composition of continuous functions as a meta operation (not itself
   a continuous function). *)
Program Definition compose_cfun {A B C} `{CPO A} `{CPO B} `{CPO C}
        (f : A -c> B) (g : B -c> C) : A -c> C :=
  {| cfun_app := fun x => cfun_app g (cfun_app f x) |}.
Next Obligation.
  intros ? ? ?; apply cfun_Proper; apply cfun_Proper; assumption.
Qed.
Next Obligation.
  destruct f, g, H1 as [? supProper]; simpl.
  rewrite cfun_Continuous0, cfun_Continuous1; apply Proper_oleq_oeq.
  unfold oeq; simpl; split; intros; reflexivity.
Qed.

Notation "f '∘' g" := (compose_cfun g f) (at level 65) : cfun_scope.
Open Scope cfun_scope.

(* A cfun parameterized by a cfun f that takes a cfun g to the cfun g ∘ f. *)
Program Definition precompose_cfun {A B C} `{CPO A} `{CPO B} `{CPO C}
        (f : A -c> B) : (B -c> C) -c> (A -c> C) :=
  {| cfun_app := fun g => g ∘ f |}.
Next Obligation.
  intros g h Hleq1 x y Hleq2.
  simpl.
  apply Hleq1. destruct f. simpl. rewrite Hleq2. reflexivity.
Qed.
Next Obligation.
  split; simpl; intros x y Hleq; destruct H1 as [? supProp]; apply supProp;
    intros n; destruct A0; simpl; destruct (x0 n) as [? cProp ?];
      apply cProp; destruct f; rewrite Hleq; reflexivity.
Qed.

(* A cfun parameterized by a cfun g that takes a cfun f to the cfun g ∘ f. *)
Program Definition postcompose_cfun {A B C} `{CPO A} `{CPO B} `{CPO C}
        (g : B -c> C) : (A -c> B) -c> (A -c> C) :=
  {| cfun_app := fun f => g ∘ f |}.
Next Obligation.
  intros ? ? Hleq1 ? ? ?; destruct g as [? cProp ?];
    apply cProp, Hleq1; auto.
Qed.
Next Obligation.
  split; simpl; intros x y Hleq; destruct g as [? gProp gCont];
    rewrite gCont; destruct H1 as [? supProp]; apply supProp; intros n;
      apply gProp; destruct A0; simpl; destruct (x0 n) as [? cProp ?];
        apply cProp; rewrite Hleq; reflexivity.
Qed.

(* A cfun parameterized by a cfun g that takes a regular function f to
   the regular function g ∘ f. *)
Program Definition postcompose_cfun' {A B C} `{CPO A} `{CPO B} `{CPO C}
        (g : B -c> C) : (A -> B) -c> (A -> C) :=
  {| cfun_app := fun f => fun x => g @c@ (f x) |}.
Next Obligation.
  simpl.
  intros f h Hleq x. destruct g. simpl.
  rewrite Hleq. reflexivity.
Qed.
Next Obligation.
  split; simpl; intros ?; destruct g as [? ? gCont];
    unfold supremum, HomSupremum; rewrite gCont;
      destruct H1 as [? supProp]; apply supProp; simpl; reflexivity.
Qed.

(* A cfun parameterized by two cfuns f and h that takes a cfun g to
   the cfun h ∘ g ∘ f. *)
Program Definition prepostcompose_cfun {A B C D} `{CPO A} `{CPO B}
        `{CPO C} `{CPO D} (f : A -c> B) (h : C -c> D)
  : (B -c> C) -c> (A -c> D) :=
  postcompose_cfun h ∘ precompose_cfun f.

(* compose_cfun is monotone. *)
Instance Proper_compose_cfun A B C `{CPO A} `{CPO B} `{CPO C} :
  Proper (oleq ==> oleq ==> oleq) (@compose_cfun A B C _ _ _ _ _ _ _ _ _).
  intros f1 f2 Rf g1 g2 Rg a1 a2 Ra.
  apply Rg. apply Rf. assumption.
Qed.


(** Lemmas for doing equational rewriting on continuous functions. *)
Lemma prepostcompose_cfun_iso {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> B) (g : C -c> D) (h : D -c> C) (k : B -c> A) :
  f ∘ k =o= id_cfun _ ->
  h ∘ g =o= id_cfun _ ->
  prepostcompose_cfun k h ∘ prepostcompose_cfun f g =o= id_cfun _.
Proof.
  intros [Heq1 Heq2] [Heq3 Heq4]; split; simpl.
  - intros x y Hleq1 ? ? Hleq2; apply Heq3, Hleq1, Heq1, Hleq2.
  - intros x y Hleq1 a b Hleq2; apply Heq4, Hleq1, Heq2, Hleq2.
Qed.

Lemma postcompose_cfun'_iso {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> B) (g : B -c> A) :
  g ∘ f =o= id_cfun _ ->
  postcompose_cfun' g ∘ postcompose_cfun' f =o= id_cfun _.
Proof. intros Heq; split; intros ? ? Hleq ?; apply Heq; auto. Qed.

Lemma compose_cfun_assoc {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> B) (g : B -c> C) (h : C -c> D) :
  h ∘ (g ∘ f) =o= (h ∘ g) ∘ f.
Proof.
  destruct f, g, h; split; simpl;
    intros ? ? Hleq; rewrite Hleq; reflexivity.
Qed.

Lemma compose_cfun_assoc' {A B C D E} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      `{CPO E} (f : A -c> B) (g : B -c> C) (h : C -c> D) (k : D -c> E) :
  (k ∘ h) ∘ (g ∘ f) =o= k ∘ (h ∘ g) ∘ f.
Proof.
  rewrite compose_cfun_assoc, <- (compose_cfun_assoc g); reflexivity.
Qed.

Lemma id_cfun_l {A B} `{CPO A} `{CPO B} (f : A -c> B) :
  id_cfun B ∘ f =o= f.
Proof. destruct f; firstorder. Qed.

Lemma id_cfun_r {A B} `{CPO A} `{CPO B} (f : A -c> B) :
  f ∘ id_cfun A =o= f.
Proof. destruct f; firstorder. Qed.

Lemma compose_cfun_iso {A B C} `{CPO A} `{CPO B} `{CPO C}
      (f : A -c> B) (g : B -c> C) (h : C -c> B) (k : B -c> A) :
  k ∘ f =o= id_cfun _ ->
  h ∘ g =o= id_cfun _ ->
  k ∘ (h ∘ g) ∘ f =o= id_cfun _.
Proof. intros ? ->; rewrite id_cfun_r; auto. Qed.

Lemma const_cfun_compose {A B C} `{CPO A} `{CPO B} `{CPO C}
      (f : A -c> B) (c : C) :
  const_cfun c ∘ f =o= const_cfun c.
Proof. split; intros; simpl; reflexivity. Qed.  

Lemma tuple_fst {A B C} `{CPO A} `{CPO B} `{CPO C}
      (f : A -c> B) (g : A -c> C) :
  fst_cfun ∘ tuple_cfun f g =o= f.
Proof. split; simpl; destruct f, g; simpl; assumption. Qed.

Lemma tuple_snd {A B C} `{CPO A} `{CPO B} `{CPO C}
      (f : A -c> B) (g : A -c> C) :
  snd_cfun ∘ tuple_cfun f g =o= g.
Proof. split; simpl; destruct f, g; simpl; assumption. Qed.

Lemma pair_fst {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> C) (g : B -c> D) :
  f ∘ fst_cfun =o= fst_cfun ∘ (pair_cfun f g).
Proof. split; intros [? ?] [? ?] [? ?]; simpl; destruct f; auto. Qed.

Lemma pair_snd {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> C) (g : B -c> D) :
  g ∘ snd_cfun =o= snd_cfun ∘ (pair_cfun f g).
Proof. split; intros [? ?] [? ?] [? ?]; simpl; destruct g; auto. Qed.

Lemma oeq_id_pointwise {A B} `{CPO A} `{CPO B} (f : A -c> B) (g : B -c> A) :
  g ∘ f =o= id_cfun A ->
  (forall x, cfun_app g (cfun_app f x) =o= x).
Proof. firstorder. Qed.

(* Continuous isomorphisms -- pairs of continuous functions whose
   composition is equivalent to identity. *)
(* NOTE: It could be cool to make isomorphism a typeclass. Symmetry
   might be a little weird, though. *)
Section isomorphism.
  Definition isomorphism {A B : Type} `{CPO A} `{CPO B}
             (f : A -c> B) (g : B -c> A) :=
    g ∘ f =o= id_cfun A /\ f ∘ g =o= id_cfun B.
  Lemma isomorphism_comm {A B : Type} `{CPO A} `{CPO B}
        (f : A -c> B) (g : B -c> A) :
    isomorphism f g -> isomorphism g f.
  Proof. firstorder. Qed.
End isomorphism.

Lemma pair_oeq {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
      (f : A -c> C) (g : B -c> D) (h : C -c> A) (k : D -c> B) :
  isomorphism f h ->
  isomorphism g k ->
  isomorphism (pair_cfun f g) (pair_cfun h k).
Proof.
  intros [Hfh1 Hfh2] [Hgk1 Hgk2].
  split; split; simpl; intros x y [Hleq1 Hleq2]; destruct x, y; split;
    try apply Hfh1; try apply Hgk1; try apply Hfh2; try apply Hgk2; auto.
Qed.

(* Program Definition proj1_cfun {A} `{CPO A} {P : A -> Prop} `{CPO {x : A | P x}} *)
(*   : {x : A | P x} -c> A := *)
(*   {| cfun_app := fun x => proj1_sig x |}. *)
(* Admit Obligations. *)
(* Next Obligation. *)
(* intros x y Hleq. destruct x. simpl in *. destruct y. *)
(* simpl in *. apply Hleq. *)

(* Section continuousProp. *)
(*   Class CProp (A : Type) : Type := *)
(*     cProp : A -> Prop. *)
(*   Class ContinuousProp (A : Type) `{CPO A} (prop : CProp A) : Prop := *)
(*     { cPropAx : forall (G : omegaChain A), *)
(*         (forall n, cProp (val G n)) <-> cProp (supremum G) }. *)
(* End continuousProp. *)


Definition cRelation A `{CPO A} := (A*A -c> Prop).

(* Definition cReflexive {A} `{CPO A} (R : cRelation A) : Prop := *)
(*   forall x, R @c@ (x, x). *)

(* Definition cTransitive {A} `{CPO A} (R : cRelation A) : Prop := *)
(*   forall x y z, R @c@ (x, y) -> R @c@ (y, z) -> R @c@ (x, z). *)

(* Definition cPreOrder {A} `{CPO A} (R : cRelation A) := *)
(*   cReflexive R /\ cTransitive R. *)

(* Definition cRelationOp A `{CPO A} := (A*A -c> PropOp). *)

(* Definition cTransitiveOp {A} `{CPO A} (R : cRelationOp A) : Prop := *)
(*   forall x y z, isTrue (R @c@ (x, y)) -> *)
(*            isTrue (R @c@ (y, z)) -> *)
(*            isTrue (R @c@ (x, z)). *)

(* Definition cSymmetricOp {A} `{CPO A} (R : cRelationOp A) : Prop := *)
(*   forall x y, isTrue (R @c@ (x, y)) -> *)
(*          isTrue (R @c@ (y, x)). *)

(* Definition cPER {A} `{CPO A} (R : cRelationOp A) := *)
(*   cSymmetricOp R /\ cTransitiveOp R. *)

(* Program Definition cRelationEmpty A `{CPO A} : cRelation A := *)
(*   const_cfun False. *)
