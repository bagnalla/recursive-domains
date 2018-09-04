Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.

Require Import Domains.Continuous Domains.Domain Domains.EPPair
        Domains.Order Domains.ProjectiveLimit.

Section cpoFunctor.
  Definition TypeF :=
    forall X (oX : OType X) (supX : Supremum X), CPO X -> Type.

  Class OTypeF (F : TypeF) : Type :=
    oTypeF :> forall X oX supX cpoX, OType (F X oX supX cpoX).

  Class SupremumF (F : TypeF) {oF : OTypeF F} : Type :=
    supremumF :> forall X oX supX cpoX, Supremum (F X oX supX cpoX).

  Class CpoF (F : TypeF) {oF : OTypeF F} {supF : SupremumF F} : Prop :=
    cpoF :> forall X oX supX cpoX, CPO (F X oX supX cpoX).

  Class EPMap (F : TypeF) {oF : OTypeF F} {supF : SupremumF F}
        {cpoF : CpoF F} : Type :=
    epMap :> forall {X Y} `{cpoX : CPO X} `{cpoY : CPO Y},
      (X -*> Y) -> (F X _ _ _) -*> (F Y _ _ _).

  Class BottomF (F : TypeF) {oF : OTypeF F} {supF : SupremumF F}
        {cpoF : CpoF F} : Type :=
    unitEPPair :> unit -*> (F unit OTunit UnitSupremum UnitCPO).

  Class CPOFunctor (F : TypeF) {oF : OTypeF F} {supF : SupremumF F}
        {cpoF : CpoF F} {epmap : EPMap F} {bottom : BottomF F} : Prop :=
    { epmap_id : forall A oA supA cpoA,
        epMap (id_ep A) =o= id_ep (F A oA supA cpoA)
    ; epmap_comp : forall A B C `{CPO A} `{CPO B} `{CPO C}
                     (f : A -*> B) (g : B -*> C),
        epMap (g ∘∘ f) =o= epMap g ∘∘ epMap f
    }.
End cpoFunctor.


Section epChainMap.
  Definition typeSequenceMap (f : nat -> Type) {g : OTypeSequence f}
             {h : SupremumSequence f} {i : CPOSequence f}
             F `{cpoFunc : CPOFunctor F}
  : nat -> Type :=
    fun n => F (f n) _ _ _.
  Instance oTypeSequenceMap
           (f : nat -> Type) {g : OTypeSequence f}
           {h : SupremumSequence f} {i : CPOSequence f}
           F `{cpoFunc : CPOFunctor F}
    : OTypeSequence (typeSequenceMap f F) :=
    fun n => oF (f n) _ _ _.
  Instance supremumSequenceMap
             (f : nat -> Type) {g : OTypeSequence f}
             {h : SupremumSequence f} {i : CPOSequence f}
             F `{cpoFunc : CPOFunctor F}
    : SupremumSequence (typeSequenceMap f F) :=
    fun n => supF (f n) _ _ _.
  Instance cpoSequenceMap
             (f : nat -> Type) {g : OTypeSequence f}
             {h : SupremumSequence f} {i : CPOSequence f}
             F `{cpoFunc : CPOFunctor F}
    : CPOSequence (typeSequenceMap f F) :=
    fun n => cpoF (f n) _ _ _.
  Instance epChainMap
             (f : nat -> Type) {g : OTypeSequence f}
             {h : SupremumSequence f} {i : CPOSequence f}
             {A : EPChain f} F `{cpoFunc : CPOFunctor F}
    : EPChain (typeSequenceMap f F) :=
    fun n => epMap (A n).
End epChainMap.


Section functorChain.
  Context (F : TypeF) {oF : OTypeF F} {supF : SupremumF F}
          {cpoF : CpoF F} {epmap : EPMap F}
          {bot : BottomF F} {cpoFunc : CPOFunctor F}.

  Record TypeWithCPO : Type :=
    { ty_ty : Type
    ; ty_otype : OType ty_ty
    ; ty_sup : Supremum ty_ty
    ; ty_cpo : CPO ty_ty
    }.

  Fixpoint typeWithCPO_n (n : nat) : TypeWithCPO :=
    match n with
    | O => {| ty_ty := unit |}
    | S n' =>
      let t := typeWithCPO_n n' in
      {| ty_ty := F _ _ _ (ty_cpo t)
       ; ty_otype := oF _ _ _ _
       ; ty_sup := supF _ _ _ _
       ; ty_cpo := cpoF _ _ _ _
      |}
    end.

  Definition type_n (n : nat) : Type :=
    ty_ty (typeWithCPO_n n).
  Definition otype_n (n : nat) : OType (type_n n) :=
    ty_otype (typeWithCPO_n n).
  Definition sup_n (n : nat) : @Supremum (type_n n) (otype_n n) :=
    ty_sup (typeWithCPO_n n).
  Definition cpo_n (n : nat) : CPO (type_n n) :=
    ty_cpo (typeWithCPO_n n).
  Program Fixpoint ep_n (n : nat) : (type_n n) -*> (type_n (S n)) :=
    match n with
    | O => _
    | S n' => epmap _ _ _ _ (cpo_n n') _ _ (cpo_n (S n')) (ep_n n')
    end.
  Next Obligation. apply bot. Defined.
End functorChain.

Instance FunctorOTypeSequence F `{CPOFunctor F}
  : OTypeSequence (type_n F) := otype_n F.
Instance FunctorSupremumSequence F `{CPOFunctor F}
  : SupremumSequence (type_n F) := sup_n F.
Instance FunctorCPOSequence F `{CPOFunctor F}
  : CPOSequence (type_n F) := cpo_n F.
Instance FunctorEPChain F `{CPOFunctor F}
  : EPChain (type_n F) := ep_n F.

(* Continuous functors (preserve colimits). *)
Section continuousFunctor.
  Class ContinuousFunctorRight F `{cpoFunc : CPOFunctor F} : Type :=
    fRight : forall f `{G : EPChain f},
      F (pLim f) _ _ _ -c> @pLim _ _ _ _ (epChainMap f F).

  Class ContinuousFunctorLeft F `{cpoFunc : CPOFunctor F} : Type :=
    fLeft : forall f `{G : EPChain f},
      @pLim _ _ _ _ (epChainMap f F) -c> F (pLim f) _ _ _.

  Class ContinuousFunctor F `{cpoFunc : CPOFunctor F}
        {cRight : ContinuousFunctorRight F}
        {cLeft : ContinuousFunctorLeft F}
    : Prop :=
    { right_left_id : forall f `{EPChain f},
        isomorphism (fLeft f) (fRight f) }.
End continuousFunctor.


Section recursiveDomain.
  Context (X : Type) `{cpoX : CPO X}.
  Class Fold F `{CpoF F}: Type := fold : F X _ _ _ -c> X.
  Class Unfold F `{CpoF F} : Type :=  unfold : X -c> F X _ _ _.
  Class RecursiveDomain F `{CpoF F} {f : Fold F} {g : Unfold F} : Prop :=
  { fold_unfold_iso : isomorphism fold unfold }.
End recursiveDomain.


Section iso_1.
  Program Definition f F `{cFunc : ContinuousFunctor F}
  : @CFun (@pLim (type_n F) _ _ _ _)
          (@pLim _ _ _ _ (epChainMap (type_n F) F))
          (OTpLim _) (PLimSupremum _) (OTpLim _) (PLimSupremum _)
    :=
      {| cfun_app := fun f => fun n => f (S n) |}.
  Next Obligation. destruct f as [f ax]; simpl; apply (ax (S n)). Qed.
  Next Obligation. intros ? ? Hleq n; apply (Hleq (S n)). Qed.
  Next Obligation.
    split; simpl; intros n; destruct (cpo_n _ (S n)) as [_ supProp];
      apply supProp; simpl; reflexivity.
  Qed.

  Program Definition g F `{cFunc : ContinuousFunctor F}
    : @CFun (@pLim _ _ _ _ (epChainMap (type_n F) F))
            (@pLim (type_n F) _ _ _ _)
            (OTpLim _) (PLimSupremum _) (OTpLim _) (PLimSupremum _) :=
    {| cfun_app := fun f => fun n => match n with
                               | O => tt
                               | S n' => f n'
                               end |}.
  Next Obligation.
    destruct n.
    - destruct (proj (chain 0) @c@ (val f0) 0); reflexivity.
    - destruct f0; simpl; apply o.
  Qed.
  Next Obligation.
    intros x y Hleq n; destruct n; try reflexivity; apply Hleq.
  Qed.
  Next Obligation.
    split; simpl; intros []; simpl; auto;
      destruct (cpo_n _ (S n)) as [_ supProp];
      apply supProp; simpl; reflexivity.
  Qed.

  Lemma f_g_iso F `{func : ContinuousFunctor F} :
    isomorphism (f F) (g F).
  Proof.
    split; unfold f, g, oeq; simpl; split; destruct n; simpl; auto.
  Qed.
End iso_1.


Instance Proper_fst {A B} {oA : OType A} {aB : OType B} : 
  Proper (@oeq (A*B) _ ==> oeq) fst.
Proof. intros [] [] []; split; simpl; try apply H; apply H0. Qed.

Instance Proper_fst_oleq {A B} {oA : OType A} {aB : OType B} : 
  Proper (@oleq (A*B) _ ==> @oleq A oA) fst.
Proof. intros [] [] []; simpl; try apply H; apply H0. Qed.

Instance Proper_snd {A B} {oA : OType A} {aB : OType B} : 
  Proper (@oeq (A*B) _ ==> oeq) snd.
Proof. intros [] [] []; split; simpl; try apply H; apply H0. Qed.

Instance Proper_cfun {A B} `{CPO A} `{CPO B} (f : A -c> B)
  : Proper (oeq ==> oeq) (@cfun_app _ _ _ _ _ _ f).
Proof. destruct f0; apply Proper_oleq_oeq. Qed.


(** From a continuous functor we can construct a recursive domain X
    with two functions fold : F X -> X and unfold : X -> F X
    witnessing the isomorphism between X and F X. *)
Section projLimit.
  Definition projLimit F `{func : CPOFunctor F} : Type :=
    pLim (type_n F).

  Instance ProjLimitFold F `{cFunc : ContinuousFunctor F}
    : Fold (pLim (type_n F)) F := g F ∘ fRight (type_n F).

  Instance ProjLimitUnfold F `{cFunc : ContinuousFunctor F}
    : Unfold (pLim (type_n F)) F := fLeft (type_n F) ∘ (f F).

  Program Instance ProjLimitRecursiveDomain F `{cFunc : ContinuousFunctor F}
    : RecursiveDomain (pLim (type_n F)) F.
  Next Obligation.
    generalize (f_g_iso F); intros [Hfg0 Hfg1]; unfold isomorphism.
    unfold fold, unfold, ProjLimitFold, ProjLimitUnfold.
    destruct cFunc; rewrite 2!compose_cfun_assoc'; split.
    - rewrite Hfg1, id_cfun_r; apply right_left_id0.
    - destruct (right_left_id0 (type_n _) _ _ _ _).
      rewrite H, id_cfun_r; apply Hfg0.
  Qed.
End projLimit.
