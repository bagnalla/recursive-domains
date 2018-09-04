Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.

Require Import Domains.Continuous Domains.Domain Domains.Order.

(** Embedding-projection pairs. These are the morphisms in the
    category Cpo^ep. We solve recursive domain equations can by taking
    suprema of ω-chains in this category ("EPChains"). *)
Section epPair.
  Record EPPair (A B : Type) `{CPO A} `{CPO B} : Type :=
    { embed : A -c> B
    ; proj  : B -c> A
    ; embed_proj_id : proj ∘ embed =o= id_cfun A
    ; proj_embed_le : embed ∘ proj <o= id_cfun B
    }.
End epPair.

Arguments embed {_ _ _ _ _ _ _ _}.
Arguments proj {_ _ _ _ _ _ _ _}.

Notation "A '-*>' B" := (EPPair A B) (right associativity, at level 99).

(* Ordering on EPPairs. *)
Instance OTEPPair {A B : Type} `{cpoA : CPO A} `{cpoB : CPO B}
  : OType (A -*> B) :=
  {| oleq := fun ep1 ep2 => embed ep1 <o= embed ep2 /\ proj ep1 <o= proj ep2 |}.
Proof.
  constructor.
  - intros ep. split; intros x y H0; destruct ep as [[] [] ? ?]; auto.
  - intros ep1 ep2 ep3 [H0 H1] [H2 H3]; split.
    + etransitivity; eauto; apply H2; reflexivity.
    + etransitivity; eauto; apply H3; reflexivity.
Defined.

(* The identity EPPair. *)
Program Definition id_ep (A : Type) `{CPO A} : A -*> A :=
  {| embed := id_cfun A; proj := id_cfun A |}.
Next Obligation. rewrite id_cfun_l; reflexivity. Qed.

(* Composition of EPPairs as a meta operation (not a continuous
   function). *)
Program Definition compose_ep
        {A B C : Type} `{cpoA : CPO A} `{cpoB : CPO B}
        `{cpoC : CPO C} (ep1 : A -*> B) (ep2 : B -*> C) : A -*> C :=
  {| embed := embed ep2 ∘ embed ep1
   ; proj  := proj ep1 ∘ proj ep2 |}.
Next Obligation.
  rewrite compose_cfun_assoc.
  rewrite <- (compose_cfun_assoc (embed ep2)).
  destruct ep2. simpl. rewrite embed_proj_id0.
  generalize id_cfun_r. intros H0.
  rewrite id_cfun_r; destruct ep1; auto.
Qed.
Next Obligation.
  cut ((embed ep2 ∘ embed ep1) ∘ (proj ep1 ∘ proj ep2) <o= id_cfun C).
  { firstorder. }
  rewrite compose_cfun_assoc.
  rewrite <- (compose_cfun_assoc (proj ep1)).
  destruct ep1. rewrite proj_embed_le0.
  rewrite id_cfun_r. destruct ep2; auto.
Qed.

Notation "f '∘∘' g" := (compose_ep g f) (at level 65) : cfun_scope.
Open Scope cfun_scope.


(* Program Definition postcompose_ep {A B C} `{CPO A} `{CPO B} `{CPO C} *)
(*         (g : B -*> C) : (A -c> B) -*> A -c> C := *)
(*   {| embed := postcompose_cfun (embed g) *)
(*    ; proj  := postcompose_cfun (proj g) |}. *)
(* Next Obligation. *)
(*   split; intros f h Hleq1 x y Hleq2; destruct g as [e p [Hep1 Hep2] Hpe]; *)
(*     simpl in *; try apply Hep1; try apply Hep2; apply Hleq1; apply Hleq2. *)
(* Qed. *)
(* Next Obligation. destruct g as [e p ? Hpe]; apply Hpe; auto. Qed. *)

Lemma id_ep_l {A B} `{CPO A} `{CPO B} (f : A -*> B) :
  id_ep B ∘∘ f =o= f.
Proof. split; split; destruct f as [[] []]; firstorder. Qed.

Lemma id_ep_r {A B} `{CPO A} `{CPO B} (f : A -*> B) :
  f ∘∘ id_ep A =o= f.
Proof. split; split; destruct f as [[] []]; firstorder. Qed.

Program Definition pair_ep {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
        (f : A -*> C) (g : B -*> D) : (A*B) -*> (C*D) :=
  {| embed := pair_cfun (embed f) (embed g)
   ; proj  := pair_cfun (proj f) (proj g) |}.
Next Obligation.
  split; split; destruct a1, a2, f as [[] []], g as [[] []];
    simpl; firstorder.
Qed.
Next Obligation.
  destruct f as [[] []], g as [[] []]; simpl; firstorder.
Qed.

(* A bit annoying to get it to use the correct types here. *)
Instance Proper_pair_ep {A B C D} `{cpoA : CPO A} `{cpoB : CPO B}
         `{cpoC : CPO C} `{cpoD : CPO D} :
  Proper (@oeq _ (@OTEPPair _ _ _ _ cpoA _ _ cpoC) ==>
               @oeq  _ (@OTEPPair _ _ _ _ cpoB _ _ cpoD) ==>
               oeq) pair_ep.
Proof.
  intros h k Heq. intros h' k' Heq'.
  split; split; intros [x1 x2] [y1 y2] [Hleq1 Hleq2]; split;
    destruct h, k, h', k', Heq as [Heq1 Heq2], Heq' as [Heq3 Heq4];
    simpl in *; try apply Heq1; try apply Heq2;
      try apply Heq3; try apply Heq4; auto.
Qed.

Lemma pair_ep_id {A B} `{cpoA : CPO A} `{cpoB : CPO B} :
  pair_ep (@id_ep _ _ _ cpoA) (@id_ep _ _ _ cpoB) =o= id_ep _.
Proof. split; split; intros [] []; firstorder. Qed.

Lemma pair_ep_compose
      {A B C D E F} `{CPO A} `{CPO B} `{CPO C} `{CPO D} `{CPO E} `{CPO F}
      (f : A -*> C) (g : B -*> D) (h : C -*> E) (k : D -*> F) :
  pair_ep (h ∘∘ f) (k ∘∘ g) =o= pair_ep h k ∘∘ pair_ep f g.
Proof.
  split; split; intros [] [] ?; split;
    destruct f as [[] []], g as [[] []], h as [[] []], k as [[] []];
    simpl; firstorder.
Qed.

Program Definition hom_ep {A B C} `{CPO A} `{CPO B} `{CPO C}
        (f : B -*> C) : (A -> B) -*> (A -> C) :=
  {| embed := postcompose_cfun' (embed f)
   ; proj  := postcompose_cfun' (proj f) |}.
Next Obligation. apply postcompose_cfun'_iso; destruct f; auto. Qed.
Next Obligation. destruct f; apply proj_embed_le0; auto. Qed.

Program Definition chom_ep {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D}
        (f : A -*> B) (g : C -*> D) : (A -c> C) -*> (B -c> D) :=
  {| embed := {| cfun_app := fun h => embed g ∘ h ∘ proj f |}
   ; proj  := {| cfun_app := fun k => proj g ∘ k ∘ embed f |} |}.
Next Obligation.
  intros h k Hleq1 x y Hleq2.
  destruct f, g. simpl.
  destruct embed1, h, proj0, k. simpl in *.
  apply cfun_Proper. apply Hleq1. rewrite Hleq2. reflexivity.
Qed.
Next Obligation.
  destruct f, g; split; simpl; intros x y Hleq; destruct embed1;
    rewrite cfun_Continuous; destruct H2; apply supremumProper;
      intros n; apply cfun_Proper; destruct A0; simpl; destruct (x0 n);
        apply cfun_Proper0; destruct proj0; rewrite Hleq; reflexivity.
Qed.
Next Obligation.
  intros h k Hleq1 x y Hleq2.
  destruct f, g. simpl.
  destruct embed0, h, proj1, k. simpl in *.
  apply cfun_Proper1. apply Hleq1. rewrite Hleq2. reflexivity.
Qed.
Next Obligation.
  destruct f, g; split; simpl; intros x y Hleq; destruct proj1;
    rewrite cfun_Continuous; destruct H1; apply supremumProper;
      intros n; apply cfun_Proper; destruct A0; simpl; destruct (x0 n);
        apply cfun_Proper0; destruct embed0; rewrite Hleq; reflexivity.
Qed.
Next Obligation.
  split; simpl; intros h k Hleq1 x y Hleq2; destruct f, g;
    apply embed_proj_id1; apply Hleq1; apply embed_proj_id0; apply Hleq2.
Qed.
Next Obligation.
  destruct f, g; apply proj_embed_le1; apply H3;
    apply proj_embed_le0; apply H4.
Qed.

Lemma chom_ep_id {A B} `{CPO A} `{CPO B} :
  chom_ep (id_ep A) (id_ep B) =o= id_ep _.
Proof. split; split; simpl; auto. Qed.

Lemma chom_ep_comp {A B C D E F} `{CPO A} `{CPO B} `{CPO C}
      `{CPO D} `{CPO E} `{CPO F}
      (f : A -*> B) (g : B -*> C)
      (h : D -*> E) (k : E -*> F) :
  chom_ep (g ∘∘ f) (k ∘∘ h) =o= chom_ep g k ∘∘ chom_ep f h.
Proof.
  split; split; simpl; intros f' g' Hleq1 x y Hleq2;
    destruct f as [[fe feProp ?] [fp fpProp ?] fep fpe];
    destruct g as [[ge geProp ?] [gp gpProp ?] gep gpe];
    destruct h as [[he heProp ?] [hp hpProp ?] hep hpe];
    destruct k as [[ke keProp ?] [kp kpProp ?] kep kpe];
    try apply keProp; try apply heProp; try apply hpProp;
      try apply kpProp; try apply keProp; try apply heProp;
        apply Hleq1; rewrite Hleq2; reflexivity.
Qed.

Lemma hom_ep_id {A B} `{CPO A} `{CPO B} :
  hom_ep (id_ep A) =o= id_ep _.
Proof. split; split; simpl; auto. Qed.

Lemma hom_ep_comp {T A B C} `{CPO T} `{CPO A} `{CPO B} `{CPO C}
      (f : A -*> B) (g : B -*> C) :
  @hom_ep T A C _ _ _ _ _ _ _ _ _ (g ∘∘ f) =o=
  hom_ep g ∘∘ hom_ep f.
Proof.
  split; split; simpl; intros h k Hleq x;
    destruct g as [[ge geProp ?] [gp gpProp ?] gep gpe];
    destruct f as [[fe feProp ?] [fp fpProp ?] fep fpe];
    try apply geProp; try apply feProp; try apply fpProp;
      try apply gpProp; apply Hleq.
Qed.

Program Definition tuple_bot_ep {A B} `{CPO A} `{CPO B}
        (f : unit -*> A) (g : unit -*> B) : unit -*> (A*B) :=
  {| embed := tuple_cfun (embed f) (embed g)
   ; proj  := const_cfun tt |}.
Next Obligation. rewrite const_cfun_compose; firstorder. Qed.
Next Obligation.
  split.
  - destruct f as [e p Hep Hpe]; simpl in *; specialize (Hpe a0 a H1);
      destruct (p @c@ a0); apply Hpe.
  - destruct g as [e p Hep Hpe]; simpl in *; specialize (Hpe b0 b H2);
      destruct (p @c@ b0); apply Hpe.
Qed.

Program Definition chom_bot_ep {A B} `{CPO A} `{CPO B}
        (ep : unit -*> B) : unit -*> (A -c> B) :=
  {| embed := const_cfun (const_cfun (embed ep @c@ tt))
   ; proj  := const_cfun tt |}.
Next Obligation. split; simpl; auto. Qed.
Next Obligation.
  destruct ep; simpl in *.
  assert (Hleq: a2 @c@ a3 <o= a2 @c@ a3) by reflexivity.
  specialize (proj_embed_le0 (a2 @c@ a3) (a2 @c@ a3) Hleq).
  destruct (proj0 @c@ (a2 @c@ a3)); apply proj_embed_le0.
Qed.

Program Definition hom_bot_ep {A B} `{CPO A} `{CPO B}
        (ep : unit -*> B) : unit -*> (A -> B) :=
  {| embed := const_cfun (fun _ => embed ep @c@ tt)
   ; proj  := const_cfun tt |}.
Next Obligation. rewrite const_cfun_compose; split; simpl; auto. Qed.
Next Obligation.
  destruct ep; simpl in *.
  assert (Hleq: a2 x <o= a2 x) by reflexivity.
  specialize (proj_embed_le0 _ _ Hleq); destruct (proj0 @c@ a2 x).
  apply proj_embed_le0.
Qed.

Lemma embed_inj {A B} `{CPO A} `{CPO B} (ep : A -*> B) x y :
  embed ep @c@ x =o= embed ep @c@ y ->
  x =o= y.
Proof.
  simpl.
  intros H1.
  destruct ep. simpl in *.
  assert (proj0 @c@ (embed0 @c@ x) =o= proj0 @c@ (embed0 @c@ y)).
  { destruct proj0. simpl. rewrite H1. reflexivity. }  
  rewrite 2!oeq_id_pointwise in H2; auto.
Qed.

Section epChain.
  Class OTypeSequence (f : nat -> Type) : Type :=
    oTypeSeq :> forall n, OType (f n).
  Class SupremumSequence (f : nat -> Type) {g : OTypeSequence f} : Type :=
    supremumSeq :> forall n, Supremum (f n).
  Class CPOSequence (f : nat -> Type) {g : OTypeSequence f}
        {h : SupremumSequence f} : Type :=
    cpoSeq :> forall n, CPO (f n).
  Class EPChain (f : nat -> Type) {g : OTypeSequence f}
        {h : SupremumSequence f} {i : CPOSequence f} : Type :=
    chain :> forall (n : nat), f n -*> f (S n).
End epChain.


Section constEPChain.
  Context (T : Type) {oT : OType T} {supT : Supremum T} {cpoT : CPO T}.
  Definition ConstTypeSequence : nat -> Type := fun _ => T.
  Global Instance ConstOTypeSequence : OTypeSequence ConstTypeSequence :=
    fun _ => oT.
  Global Instance ConstSupremumSequence : SupremumSequence ConstTypeSequence :=
    fun _ => supT.
  Global Instance ConstCPOSequence : CPOSequence ConstTypeSequence :=
    fun _ => cpoT.
  Global Instance ConstEPChain : EPChain ConstTypeSequence :=
    fun n => id_ep T.
End constEPChain.


(** Product EP chain. *)
Definition ProductTypeSequence (f1 f2 : nat -> Type) : nat -> Type :=
  fun n => prod (f1 n) (f2 n).

Instance ProductOTypeSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
  : OTypeSequence (ProductTypeSequence f1 f2) :=
  fun n => @OTpair _ _ (g1 n) (g2 n).

Instance ProductSupremumSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
         (h1 : SupremumSequence f1) (h2 : SupremumSequence f2)
  : SupremumSequence (ProductTypeSequence f1 f2) :=
  fun n => ProductSupremum (f1 n) (f2 n).

Instance ProductCPOSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
         {h1 : SupremumSequence f1} {h2 : SupremumSequence f2}
         (i1 : CPOSequence f1) (i2 : CPOSequence f2)
  : CPOSequence (ProductTypeSequence f1 f2) :=
  fun n => ProductCPO (f1 n) (f2 n).

Instance ProductEPChain `(e1 : EPChain) `(e2 : EPChain) :
  EPChain (ProductTypeSequence f f0) :=
  fun n => pair_ep (chain n) (chain n).


(** Constant LHS continuous function space EP chain. *)
Definition ConstHomTypeSequence T `{CPO T} (f : nat -> Type)
           {g : OTypeSequence f} {h : SupremumSequence f}
           {i : CPOSequence f} : nat -> Type :=
  fun n => T -> f n.

Instance ConstHomOTypeSequence T `{CPO T} (f : nat -> Type)
         {g : OTypeSequence f} {h : SupremumSequence f}
         {i : CPOSequence f} : OTypeSequence (ConstHomTypeSequence T f) :=
  fun n => _.

Instance ConstHomSupremumSequence T `{CPO T} (f : nat -> Type)
         {g : OTypeSequence f} {h : SupremumSequence f}
         {i : CPOSequence f} : SupremumSequence (ConstHomTypeSequence T f) :=
  fun n => _.

Instance ConstHomCPOSequence T `{CPO T} (f : nat -> Type)
         {g : OTypeSequence f} {h : SupremumSequence f}
         {i : CPOSequence f} : CPOSequence (ConstHomTypeSequence T f) :=
  fun n => _.

Instance ConstHomEPChain T `{CPO T} `(G : EPChain)
  : EPChain (ConstHomTypeSequence T f) :=
  fun n => hom_ep (chain n).

(** Continuous function space EP chain. *)
Definition HomTypeSequence (f1 f2 : nat -> Type)
           {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
           {h1 : SupremumSequence f1} {h2 : SupremumSequence f2}
           {i1 : CPOSequence f1} {i2 : CPOSequence f2} : nat -> Type :=
  fun n => f1 n -c> f2 n.

Instance HomOTypeSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
         {h1 : SupremumSequence f1} {h2 : SupremumSequence f2}
         (i1 : CPOSequence f1) (i2 : CPOSequence f2)
  : OTypeSequence (HomTypeSequence f1 f2) :=
  fun n => _.

Instance HomSupremumSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
         {h1 : SupremumSequence f1} {h2 : SupremumSequence f2}
         (i1 : CPOSequence f1) (i2 : CPOSequence f2)
  : SupremumSequence (HomTypeSequence f1 f2) :=
  fun n => _.

Instance HomCPOSequence (f1 f2 : nat -> Type)
         {g1 : OTypeSequence f1} {g2 : OTypeSequence f2}
         {h1 : SupremumSequence f1} {h2 : SupremumSequence f2}
         (i1 : CPOSequence f1) (i2 : CPOSequence f2)
  : CPOSequence (HomTypeSequence f1 f2) :=
  fun n => _.

Instance HomEPChain `(e1 : EPChain) `(e2 : EPChain)
  : EPChain (HomTypeSequence f f0) :=
  fun n => chom_ep (chain n) (chain n).
