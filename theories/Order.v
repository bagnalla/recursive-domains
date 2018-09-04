Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Le.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Coq.Program.Equality.

(* A class for types equipped with a preorder relation. *)
Class OType (A : Type) : Type :=
  { oleq : relation A
  ; oPreOrder :> PreOrder oleq
  }.

Instance OType_Reflexive A `{OType A} : Reflexive oleq.
Proof. typeclasses eauto. Qed.

Instance OType_Transitive A `{OType A} : Transitive oleq.
Proof. typeclasses eauto. Qed.

(* The equivalence relation induced by the symmetric closure of the
   preorder relation. *)
Definition oeq {A} `{OType A} : relation A :=
  fun x y => oleq x y /\ oleq y x.

Lemma oeq_refl A (o : OType A) x : oeq x x.
Proof. firstorder. Qed.

Lemma oeq_symm A (o : OType A) x y : oeq x y -> oeq y x.
Proof. firstorder. Qed.

Lemma oeq_trans A (oA : OType A) x y z : oeq x y -> oeq y z -> oeq x z.
Proof.
  simpl. intros [H0 H1] [H2 H3].
  destruct oA as [? [? trans]].
  split; eapply trans; eauto.
Qed.

Add Parametric Relation
    {A : Type} `{o : OType A} : A oeq
    reflexivity proved by (@oeq_refl A o)
    symmetry proved by (@oeq_symm A o)
    transitivity proved by (@oeq_trans A o)
      as oleq_rel.

Instance Proper_oleq A `{OType A} :
  Proper (oeq ==> oeq ==> iff) oleq.
Proof.
  intros a b ? c d ?; split; intros ?.
  - transitivity a; firstorder. transitivity c; eauto.
  - transitivity b; firstorder. transitivity d; eauto.
Qed.

Instance Proper_oeq A `{OType A} :
  Proper (oeq ==> oeq ==> iff) oeq.
Proof.
  intros a b ? c d ?; split; intros ?.
  - transitivity a; firstorder. transitivity c; eauto.
    etransitivity; eauto.
  - transitivity b; firstorder. transitivity d; eauto.
    etransitivity; eauto.
Qed.

Notation "x <o= y" := (oleq x y) (no associativity, at level 70).
Notation "x =o= y" := (oeq x y) (no associativity, at level 70).
Notation "'val' x" := (proj1_sig x) (at level 10).


(* The pointwise ordering on pairs *)
Instance OTpair A B `{OType A} `{OType B} : OType (A*B) :=
  {| oleq := fun p1 p2 => oleq (fst p1) (fst p2) /\ oleq (snd p1) (snd p2) |}.
Proof.
  repeat constructor.
  - destruct x; reflexivity.
  - destruct x; reflexivity.
  - destruct x, y, z, H1, H2; transitivity a0; assumption.
  - destruct x, y, z, H1, H2; transitivity b0; assumption.
Defined.

(* Lift order relation to subset types by ignoring the proof term. *)
Instance OTsubset A `{OType A} {P : A -> Prop} : OType {a : A | P a} :=
  {| oleq := fun x y => val x <o= val y |}.
Proof.
  constructor.
  - firstorder.
  - unfold Transitive. etransitivity; eauto.
Defined.

Lemma exist_proper {A : Type} `{OType A} {P : A -> Prop}
      (a b : {x : A | P x}) :
  proj1_sig a =o= proj1_sig b -> a =o= b.
Proof. firstorder. Qed.

Program Instance OTarrow A B {oB : OType B} : OType (A -> B) :=
  {| oleq := fun f g => forall x, f x <o= g x |}.
Next Obligation.
  constructor. firstorder.
  intros ?; etransitivity; eauto.
Defined.

(* Instance Proper_id_oleq X `{OType X} : *)
(*   Proper (oleq ==> oleq) (fun x : X => x). *)
(* Proof. firstorder. Qed. *)
(* Instance Proper_id_oeq X `{OType X} : *)
(*   Proper (oeq ==> oeq) (fun x : X => x). *)
(* Proof. firstorder. Qed. *)

Instance Proper_pair {X Y} {oX : OType X} {oY : OType Y} :
  Proper (oeq ==> oeq ==> oeq) (@pair X Y).
Proof. firstorder. Qed.

Instance Proper_pair_oleq {X Y} {oX : OType X} {oY : OType Y} :
  Proper (oleq ==> oleq ==> oleq) (@pair X Y).
Proof. firstorder. Qed.

(* Monotonicity implies properness wrt oeq. *)
Instance Proper_oleq_oeq {A B : Type} {oA : OType A} {oB : OType B}
         {f : A -> B} {pf : Proper (oleq ==> oleq) f} :
  Proper (oeq ==> oeq) f.
Proof. firstorder. Qed.

Instance Proper_oleq_oeq2
         {A B C : Type} {oA : OType A} {oB : OType B} {oC : OType C}
         {f : A -> B -> C} {pf : Proper (oleq ==> oleq ==> oleq) f} :
  Proper (oeq ==> oeq ==> oeq) f.
Proof. firstorder. Qed.

Lemma pair_oeq_inv {A B : Type} {oA : OType A} {oB : OType B}
      (x1 x2 : A) (y1 y2 : B) :
  (x1, y1) =o= (x2, y2) ->
  x1 =o= x2 /\ y1 =o= y2.
Proof. firstorder. Qed.

(* Inductive PropOp := *)
(* | propOp : Prop -> PropOp. *)

(* Definition isTrue (P : PropOp) := match P with | propOp P' => P' end. *)

Program Instance OTprop : OType Prop :=
  {| oleq := impl |}.
Next Obligation. firstorder. Defined.

(* Program Instance OTpropOp : OType PropOp := *)
(*   {| oleq := fun x y => *)
(*                match x, y with *)
(*                | propOp P, propOp Q => Q -> P *)
(*                end |}. *)
(* Next Obligation. *)
(*   constructor. *)
(*   - intros []; auto. *)
(*   - intros [] [] []; auto. *)
(* Defined. *)
