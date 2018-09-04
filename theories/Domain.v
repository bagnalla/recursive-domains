Require Import Coq.Classes.Morphisms.

Require Import Domains.Order.

(* ω-chains are ascending sequences of elements. *)
Section omegaChain.
  Context (X : Type) {o : OType X}.

  Definition omegaAx (g : nat -> X) := forall j, oleq (g j) (g (S j)).
  Definition omegaChain := { g : nat -> X | omegaAx g }.

  Definition upper_bound (x : X) (A : omegaChain) :=
    forall j, val A j <o= x.

  Definition is_supremum (x : X) (A : omegaChain) :=
    upper_bound x A /\
    forall b, upper_bound b A -> x <o= b.
End omegaChain.

Arguments is_supremum {_ _}.
Arguments upper_bound {_ _}.

(* OType instance for ω-chains. *)
Instance omegaChainOType X {oX : OType X} : OType (@omegaChain X oX) :=
  {| oleq := fun x y => forall n, val x n <o= val y n |}.
Proof.
  constructor.
  - firstorder.
  - intros ? ? ?; etransitivity; eauto.
Defined.

(* Map a function over an ω-chain. *)
Program Definition omegaChainMap {X Y : Type} {oX : OType X} {oY : OType Y}
        (f : X -> Y) (pf : Proper (oleq ==> oleq) f) (A : @omegaChain X oX)
  : @omegaChain Y oY:=
  fun n => f (A n).
Next Obligation. intros j; destruct A; apply pf; auto. Qed.

(* omegaChainMap preserves identity. *)
Lemma omegaChainMap_id {X : Type} {oX : OType X} (A : @omegaChain X oX)
      (pf : Proper (oleq ==> oleq) (fun x : X => x)) :
  omegaChainMap (fun x => x) pf A =o= A.
Proof. split; intros n; reflexivity. Qed.

(* Split/unzip an ω-chain.  *)
Program Definition splitChain {X Y : Type}
        (oX : OType X) `(oY : OType Y)
        (A : @omegaChain (X*Y)%type _)
  : @omegaChain X oX * @omegaChain Y oY :=
  (fun n => fst (A n), fun n => snd (A n)).
Next Obligation.
  intros j; destruct A; simpl; specialize (o j).
  destruct (x j), (x (S j)); firstorder.
Qed.
Next Obligation.
  intros j; destruct A; simpl; specialize (o j).
  destruct (x j), (x (S j)); firstorder.
Qed.


(* ω-complete partial orders, either pointed or not. *)
Section cpo.
  Context (X : Type) {o : OType X}.
  Class Supremum : Type :=
    supremum : omegaChain X -> X.
  Class CPO {sup : Supremum} : Prop :=
    { supremumAx : forall A : omegaChain X, is_supremum (supremum A) A
    ; supremumProper : Proper (oleq ==> oleq) sup }.
  Class Bottom : Type :=
    bot : X.
  Class PointedCPO `{cpo : CPO} {b : @Bottom} : Prop :=
    { botAx : forall (x : X), bot <o= x }.
End cpo.

Instance OTbot X {oX : OType X} : OType (Bottom X) := oX.
Instance supremumBot X `{supX : Supremum X} : Supremum (Bottom X) := supX.
Instance cpoBot X `{cpoX : CPO X} : CPO (Bottom X) := cpoX.

Arguments supremum {_ _ _}.
Arguments bot {_ _}.

(* General construction for the supremum operation of a product CPO. *)
Instance ProductSupremum X Y {oX : OType X} {oY : OType Y}
         {supX : Supremum X} {supY : Supremum Y} : Supremum (X*Y) :=
  fun A => let (A1, A2) := splitChain _ _ A in (supX A1, supY A2).

(* The product supremum is monotone. *)
Instance ProductSupremum_Proper X Y {oX : OType X} {oY : OType Y}
         {supX : @Supremum X oX} {supY : @Supremum Y oY}
         {cpoX : CPO X} {cpoY : CPO Y}
  :
  Proper (oleq ==> oleq) (@ProductSupremum X Y oX oY supX supY).
Proof.
  intros x1 x2 Heq; apply Proper_pair_oleq.
  - assert ((exist (fun g : nat -> X => omegaAx _ g) (fun n : nat => fst ((val x1) n))
                   (splitChain_obligation_1 X Y oX oY x1)) <o=
            (exist (fun g : nat -> X => omegaAx _ g) (fun n : nat => fst ((val x2) n))
                   (splitChain_obligation_1 X Y oX oY x2))) by firstorder.
    destruct cpoX; firstorder.
  - assert ((exist (fun g : nat -> Y => omegaAx _ g) (fun n : nat => snd ((val x1) n))
                   (splitChain_obligation_2 X Y oX oY x1)) <o=
            (exist (fun g : nat -> Y => omegaAx _ g) (fun n : nat => snd ((val x2) n))
                   (splitChain_obligation_2 X Y oX oY x2))) by firstorder.
    destruct cpoY; firstorder.
Qed.

(* The product supremum satisfies the CPO axioms. *)
Instance ProductCPO X Y `{cpoX : CPO X} `{cpoY : CPO Y} : CPO (X*Y).
Proof.
  constructor.
  - intros A; destruct cpoX, cpoY.
    specialize (supremumAx0 (fst (splitChain _ _ A))).
    specialize (supremumAx1 (snd (splitChain _ _ A))).
    split; firstorder.
  - intros ? ? ->; reflexivity.
Qed.

(* The Prop CPO. *)
Instance PropSupremum : @Supremum Prop _ := fun G => exists n, val G n.
Program Instance PropCPO : CPO Prop.
Solve Obligations with firstorder.
Instance PropBottom : Bottom Prop := False.
Program Instance PropPointedCPO : PointedCPO Prop.
Solve Obligations with firstorder.

(* Instance PropOpSupremum : @Supremum PropOp _ := *)
(*   fun G => propOp (forall n, isTrue (val G n)). *)

(* (* TODO: cleanup *) *)
(* Program Instance PropOpCPO : CPO PropOp. *)
(* Next Obligation. *)
(*   split. *)
(*   - intros j. simpl. *)
(*     destruct A. simpl. destruct (x j) eqn:Hx. *)
(*     intros H. specialize (H j). unfold isTrue in H. *)
(*     rewrite Hx in H. auto. *)
(*   - intros b Hub. simpl. destruct b. intros Hp n. *)
(*     unfold isTrue. unfold upper_bound in Hub. *)
(*     specialize (Hub n). simpl in Hub. *)
(*     destruct A. simpl in *. *)
(*     destruct (x n); auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros x y Hleq H n. *)
(*   destruct x. simpl in *. *)
(*   specialize (Hleq n). *)
(*   destruct (x n). simpl in *. *)
(*   destruct y. simpl in *. *)
(*   destruct (x0 n) eqn:Hx0. simpl in *. *)
(*   apply Hleq. *)
(*   specialize (H n). rewrite Hx0 in H. simpl in H. *)
(*   auto. *)
(* Qed. *)

(* Instance PropOpBottom : Bottom PropOp := propOp True. *)
(* Program Instance PropOpPointedCPO : PointedCPO PropOp. *)
(* Next Obligation. destruct x. auto. Qed. *)

(* Pointwise application of an ω-chain of functions to a fixed
   argument, yielding an ω-chain of codomain values. *)
Program Definition apply_chain {A B : Type} (* `{cpoA : CPO A} `{cpoB : CPO B} *)
        `{Supremum A} `{Supremum B}
        (ch : @omegaChain (A -> B) _) (x : A)
  : @omegaChain B _ := fun n => (ch n) x.
Next Obligation.
  intros j; destruct ch as [ch ax]; apply ax; reflexivity.
Qed.

(* Supremum and CPO instances for non-continuous function spaces. *)
Instance HomSupremum A B `{Supremum A} `{supB : Supremum B}
  : @Supremum (A -> B) (OTarrow _ _) :=
  fun ch => fun x => supB (apply_chain ch x).

Instance HomCPO A B `{cpoA : CPO A} `{cpoB : CPO B} : CPO (A -> B).
Proof.
  constructor.
  - intros G. split.
    + intros j x; destruct cpoB as [supAx ?]; edestruct supAx.
      specialize (H j); etransitivity.
      shelve. apply H. Unshelve. reflexivity.
    + intros b Hub x; destruct cpoB as [supAx ?]; edestruct supAx.
      apply H0; intros j; apply Hub.
  - intros f g Hleq x; destruct cpoB as [? supProp]; apply supProp.
    intros n; destruct f, g; apply Hleq.
Qed.


(** Unit type CPO. *)
Instance OTunit : OType unit :=
  {| oleq := fun _ _ => True |}.
Proof. firstorder. Defined.
Instance UnitSupremum : Supremum unit := fun _ => tt.
Program Instance UnitCPO : CPO unit.
Next Obligation.
  unfold supremum, UnitSupremum, is_supremum, upper_bound;
    destruct A; simpl; split.
  - intros j; destruct (x j); reflexivity.
  - intros []; reflexivity.
Qed.
Next Obligation. intros ? ? ?; reflexivity. Qed.


(* Program Definition proj1_chain {A : Type} `{CPO A} {P} *)
(*         (G : @omegaChain {x : A | P x} _) *)
(*   : @omegaChain A _ := fun n => proj1_sig (G n). *)
(* Next Obligation. destruct G; simpl; firstorder. Qed.       *)

(* Program Instance SubsetSupremum {A} `{CPO A} P : @Supremum {x : A | P x} _ := *)
(*   fun G => supremum (proj1_chain G). *)
(* Next Obligation. *)