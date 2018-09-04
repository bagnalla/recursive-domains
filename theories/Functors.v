Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Require Import Domains.Continuous Domains.Domain Domains.EPPair
        Domains.FunctorClasses Domains.Order Domains.ProjectiveLimit.


Section constFunctor.
  Context (X : Type) {o : OType X} {bot : Bottom X} {supr : Supremum X}
          {cpo : CPO X} {pcpo : PointedCPO X}.
  Definition ConstTypeF : TypeF := fun _ _ _ _ => X.
  Global Instance ConstOTypeF : OTypeF _ := fun _ _ _ _ => o.
  Global Instance ConstSupremumF : SupremumF _ := fun _ _ _ _ => supr.
  Global Instance ConstCpoF : CpoF _ := fun _ _ _ _ => cpo.
  Global Instance ConstEPMap : EPMap _ := fun _ _ _ _ _ _ _ _ _ => id_ep X.
  Global Program Instance ConstBottomF : BottomF ConstTypeF :=
    {| embed := const_cfun bot
     ; proj  := const_cfun tt |}.
  Next Obligation.
    split; unfold const_cfun, compose_cfun; simpl.
    - intros ? x ?; destruct x; reflexivity.
    - intros x ? ?; destruct x; reflexivity.
  Qed.
  Next Obligation. eapply botAx; eauto. Qed.
  Global Program Instance ConstCPOFunctor : CPOFunctor ConstTypeF.
  Next Obligation. reflexivity. Qed.
  Next Obligation. rewrite id_ep_l; reflexivity. Qed.
  Global Program Instance ConstFunctorRight : ContinuousFunctorRight _ :=
    fun _ _ _ _ _ => {| cfun_app := fun t => fun _ => t |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. intros ?; auto. Qed.
  Next Obligation.
    split; simpl.
    - intros n; pose proof cpo as Hcpo; destruct Hcpo as [_ supProp].
      apply supProp; simpl; reflexivity.
    - intros n; pose proof cpo as Hcpo; destruct Hcpo as [_ supProp].
      apply supProp; simpl; reflexivity.
  Qed.
  Global Program Instance ConstFunctorLeft : ContinuousFunctorLeft _ :=
    fun _ _ _ _ _ => {| cfun_app := fun f => proj1_sig f 0 |}.
  Next Obligation. intros ? ? ->; reflexivity. Qed.
  Next Obligation.
    unfold supremum, supremumF, ConstSupremumF.
    pose proof cpo as Hcpo; destruct Hcpo as [_ ?].
    apply Proper_oleq_oeq; split; simpl; reflexivity.
  Qed.
  Global Program Instance ConstContinuousFunctor
    : ContinuousFunctor ConstTypeF.
  Next Obligation.
    split; split; simpl; auto.
    - intros x y Hleq; induction n.
      + apply Hleq.
      + destruct x, y; simpl in *; rewrite <- o1; apply IHn.
    - intros x y Hleq; induction n.
      + apply Hleq.
      + destruct x, y; simpl in *; rewrite <- o0; apply IHn.
  Qed.
End constFunctor.


(* Any type is isomorphic to the projective limit of the constant
   functor applied to that type. *)
Section constIsomorphism.
  Context (X : Type) {o : OType X} {bot : @Bottom X} {supr : Supremum X}
          {cpo : CPO X} {pcpo : PointedCPO X}.

  Program Definition constFold : X -c> pLim (type_n (ConstTypeF X)) :=
    {| cfun_app := fun x => fun n => match n with
                               | O => tt
                               | S _ => x
                               end |}.
  Admit Obligations.

  Program Definition constUnfold : pLim (type_n (ConstTypeF X)) -c> X :=
    {| cfun_app := fun h => h 1 |}.
  Admit Obligations.

  Lemma constIsomorphism :
    isomorphism constFold constUnfold.
  Proof.
    split.
    - split; simpl; auto.
    - split; simpl.
      + intros f g Hleq []; simpl; auto; induction n.
        * apply Hleq.
        * destruct g; simpl in *; etransitivity.
          -- apply IHn.
          -- rewrite o0; reflexivity.
      + intros f g Hleq []; simpl; auto.
        induction n.
        * apply Hleq.
        * destruct f; simpl in *; rewrite o0 in IHn; apply IHn.
  Qed.
End constIsomorphism.


Section idFunctor.
  Definition IdTypeF : TypeF := fun X _ _ _ => X.
  Global Instance IdOTypeF : OTypeF _ := fun _ o _ _ => o.
  Global Instance IdSupremumF : SupremumF _ := fun _ _ sup _ => sup.
  Global Instance IdCpoF : CpoF _ := fun _ _ _ cpo => cpo.
  Global Instance IdEPMap : EPMap _ := fun _ _ _ _ _ _ _ _ ep => ep.
  Global Program Instance IdBottomF : BottomF IdTypeF :=
    {| embed := id_cfun _
     ; proj  := id_cfun _ |}.
  Next Obligation. rewrite id_cfun_l; reflexivity. Qed.
  Global Program Instance IdCPOFunctor : CPOFunctor IdTypeF.
  Solve Obligations with reflexivity.
  Global Instance IdFunctorRight : ContinuousFunctorRight _ :=
    fun _ _ _ _ _ => id_cfun _.
  Global Instance IdFunctorLeft : ContinuousFunctorLeft _ :=
    fun _ _ _ _ _ => id_cfun _.
  Global Program Instance IdContinuousFunctor : ContinuousFunctor _.
  Next Obligation. split; rewrite id_cfun_l; reflexivity. Qed.
End idFunctor.


Section productFunctor.
  Context (F1 : TypeF) {oF1 : OTypeF F1} {supF1 : SupremumF F1}
          {cpoF1 : CpoF F1} {epmap1 : EPMap F1}
          {bot1 : BottomF F1} {cpoFunc1 : CPOFunctor F1}
          {left1 : ContinuousFunctorLeft F1}
          {right1 : ContinuousFunctorRight F1}
          {cFunc1 : ContinuousFunctor F1}
          (F2 : TypeF) {oF2 : OTypeF F2} {supF2 : SupremumF F2}
          {cpoF2 : CpoF F2} {epmap2 : EPMap F2}
          {bot2 : BottomF F2} {cpoFunc2 : CPOFunctor F2}
          {left2 : ContinuousFunctorLeft F2}
          {right2 : ContinuousFunctorRight F2}
          {cFunc2 : ContinuousFunctor F2}.

  Definition ProductTypeF : TypeF :=
    fun X o sup cpo => prod (F1 X o sup cpo) (F2 X o sup cpo).

  Global Program Instance ProductOTypeF : OTypeF ProductTypeF :=
    fun X o sup cpo => @OTpair _ _ (oF1 X o sup cpo) (oF2 X o sup cpo).

  Global Instance ProductSupremumF : SupremumF _ :=
    fun X o sup cpo =>
      ProductSupremum (F1 X o sup cpo) (F2 X o sup cpo).

  Global Instance ProductCpoF : CpoF _ :=
    fun _ _ _ _  => ProductCPO (F1 _ _ _ _) (F2 _ _ _ _).

  Global Instance ProductEPMap : EPMap ProductTypeF :=
    fun _ _ _ _ _ _ _ _ ep => pair_ep (epMap ep) (epMap ep).

  Global Instance ProductBottomF : BottomF _ := tuple_bot_ep bot1 bot2.
  Global Program Instance ProductCPOFunctor : CPOFunctor ProductTypeF.
  Next Obligation.
    unfold epMap, ProductEPMap; destruct cpoFunc1, cpoFunc2.
    rewrite epmap_id, epmap_id0; apply pair_ep_id.
  Qed.
  Next Obligation.
    unfold epMap, ProductEPMap; destruct cpoFunc1, cpoFunc2.
    rewrite epmap_comp, epmap_comp0; apply pair_ep_compose.
  Qed.
  Global Instance ProductFunctorRight :
    ContinuousFunctorRight ProductTypeF :=
    fun _ _ _ _ G =>
      (pLim_intro (product_cone (cone_id _) (cone_id _)))
        ∘ (pair_cfun (fRight _) (fRight _)).

  Global Instance ProductFunctorLeft :
    ContinuousFunctorLeft ProductTypeF :=
    fun F _ _ _ _ =>
      (pair_cfun (fLeft _) (fLeft _))
        ∘ tuple_cfun (pLim_intro (proj1_cone (cone_id _)))
        (pLim_intro (proj2_cone (cone_id _))).

  Global Program Instance ProductContinuousFunctor
    : ContinuousFunctor ProductTypeF.
  Next Obligation.
    unfold fLeft, fRight, ProductFunctorLeft, ProductFunctorRight.
    assert (isomorphism (pair_cfun (right1 _ _ _ _ _) (right2 _ _ _ _ _))
                        (pair_cfun (fLeft f) (fLeft f))).
    { destruct cFunc1, cFunc2.
      apply pair_oeq; apply isomorphism_comm.
      - apply right_left_id.
      - apply right_left_id0. }
    split.
    - rewrite compose_cfun_assoc'.
      destruct H0 as [? H1]; rewrite H1; apply pLim_product_sound.
    - rewrite compose_cfun_assoc'; apply compose_cfun_iso.
      * apply H0.
      * split; simpl; intros [] [] []; split; auto.
  Qed.
End productFunctor.


Section constHomFunctor.
  Context (T : Type) {oT : OType T} {supT : Supremum T} {cpoT : CPO T}.
  Context (F : TypeF) {oF : OTypeF F} {supF : SupremumF F}
          {cpoF : CpoF F} {epmap : EPMap F}
          {bot : BottomF F} {cpoFunc : CPOFunctor F}
          {left : ContinuousFunctorLeft F}
          {right : ContinuousFunctorRight F}
          {cFunc : ContinuousFunctor F}.

  Definition ConstHomTypeF : TypeF :=
    fun X o sup cpo => T -> (F X o sup cpo).

  Global Instance ConstHomOTypeF : OTypeF ConstHomTypeF :=
    fun X o sup cpo => OTarrow T (F X o sup cpo).

  Global Instance ConstHomSupremumF : SupremumF ConstHomTypeF :=
    fun X o sup cpo => HomSupremum T (F X o sup cpo).

  Global Instance ConstHomCpoF : CpoF ConstHomTypeF :=
    fun _ _ _ _ => HomCPO _ _.

  Global Instance ConstHomEPMap : EPMap ConstHomTypeF :=
    fun _ _ _ _ _ _ _ _ ep => hom_ep (epMap ep).

  Global Instance ConstHomBottomF : BottomF ConstHomTypeF :=
    hom_bot_ep bot.

  Global Instance Proper_const_hom_ep {A B C} `{CPO A} `{CPO B} `{CPO C} :
    Proper (@oeq (B -*> C) _ ==> @oeq ((A -> B) -*> (A -> C)) _) hom_ep.
  Proof.
    intros f g Heq. split; split; simpl; intros h k Hleq x;
      destruct Heq as [[Heq1 Heq2] [Heq3 Heq4]]; try apply Heq1;
        try apply Heq2; try apply Heq3; try apply Heq4; apply Hleq.
  Qed.

  Global Program Instance ConstHomCPOFunctor : CPOFunctor ConstHomTypeF.
  Next Obligation.
    unfold epMap, ConstHomEPMap.
    destruct cpoFunc. rewrite epmap_id.
    apply hom_ep_id.
  Qed.
  Next Obligation.
    unfold epMap, ConstHomEPMap.
    destruct cpoFunc. rewrite epmap_comp.
    apply hom_ep_comp.
  Qed.

  Global Instance ConstHomFunctorRight :
    ContinuousFunctorRight ConstHomTypeF :=
    fun f _ _ _ _ =>
      pLim_const_lambda T (typeSequenceMap f F) ∘ postcompose_cfun' (fRight _).

  Global Program Instance ConstHomFunctorLeft :
    ContinuousFunctorLeft ConstHomTypeF :=
    fun f _ _ _ _ =>
      postcompose_cfun' (fLeft _) ∘ pLim_const_apply T (typeSequenceMap f F).

  Global Program Instance ConstHomContinuousFunctor
    : ContinuousFunctor ConstHomTypeF.
  Next Obligation.
    unfold fLeft, fRight, ConstHomFunctorLeft, ConstHomFunctorRight.
    split; rewrite compose_cfun_assoc'; apply compose_cfun_iso.
    - (* Not sure why this won't infer the correct types. It applies
         successfully in the other case below... *)
      generalize (@pLim_const_lambda_apply_iso T _ _ _ _ _ _ _
                                               (epChainMap f F)).
      intros [_ H0]; apply H0.
    - apply postcompose_cfun'_iso; destruct cFunc; apply right_left_id.
    - apply postcompose_cfun'_iso; destruct cFunc; apply right_left_id.
    - apply pLim_const_lambda_apply_iso.
  Qed.
End constHomFunctor.


Section homFunctor.
  Context (F1 : TypeF) {oF1 : OTypeF F1} {supF1 : SupremumF F1}
          {cpoF1 : CpoF F1} {epmap1 : EPMap F1}
          {bot1 : BottomF F1} {cpoFunc1 : CPOFunctor F1}
          {left1 : ContinuousFunctorLeft F1}
          {right1 : ContinuousFunctorRight F1}
          {cFunc1 : ContinuousFunctor F1}
          (F2 : TypeF) {oF2 : OTypeF F2} {supF2 : SupremumF F2}
          {cpoF2 : CpoF F2} {epmap2 : EPMap F2}
          {bot2 : BottomF F2} {cpoFunc2 : CPOFunctor F2}
          {left2 : ContinuousFunctorLeft F2}
          {right2 : ContinuousFunctorRight F2}
          {cFunc2 : ContinuousFunctor F2}.

  Definition HomTypeF : TypeF :=
    fun X o sup cpo => F1 X o sup cpo -c> F2 X o sup cpo.

  Global Instance HomOTypeF : OTypeF HomTypeF :=
    (* fun X o sup => @OTcarrow (F1 X o sup) (F2 X o sup) _ _ _ _. *)
    fun X o sup cpo => OTcarrow (F1 X o sup cpo) (F2 X o sup cpo).

  Global Instance HomSupremumF : SupremumF HomTypeF :=
    fun X o sup cpo => ContinuousHomSupremum (supF1 X o sup cpo)
                                          (supF2 X o sup cpo).

  Global Instance HomCpoF : CpoF HomTypeF :=
    fun _ _ _ _ => ContinuousHomCPO _ _.

  Global Instance HomEPMap : EPMap HomTypeF :=
    fun _ _ _ _ _ _ _ _ ep => chom_ep (epMap ep) (epMap ep).

  Global Instance HomBottomF : BottomF HomTypeF :=
    chom_bot_ep bot2.

  Global Instance Proper_hom_ep {A B C D} `{CPO A} `{CPO B} `{CPO C} `{CPO D} :
    Proper (@oeq (A -*> C) _ ==> @oeq (B -*> D) _ ==> oeq) chom_ep.
  Proof.
    intros x y Heq; split; split; simpl; intros f g Hleq1 a b Hleq2;
        destruct x0 as [[] ? ? ?], y0 as [[] ? ? ?];
        destruct H3 as [[Heq0 Heq1] [Heq2 Heq3]];
        try apply Heq0; try apply Heq1; try apply Heq2;
          try apply Heq3; apply Hleq1; destruct x, y;
            destruct Heq as [[Heq4 Heq5] [Heq6 Heq7]];
            try apply Heq4; try apply Heq5; try apply Heq6;
              try apply Heq7; apply Hleq2.
  Qed.

  Global Instance HomCPOFunctor : CPOFunctor HomTypeF.
  Proof.
    constructor.
    - intros X oX supX cpoX; unfold epMap, HomEPMap.
      destruct cpoFunc1, cpoFunc2; rewrite epmap_id, epmap_id0.
      apply chom_ep_id.
    - intros A B C oA supA cpoA oB supB cpoB oC supC cpoC f g.
      unfold epMap, HomEPMap; destruct cpoFunc1, cpoFunc2.
      rewrite epmap_comp, epmap_comp0; apply chom_ep_comp.
  Qed.

  Global Program Instance HomFunctorRight :
    ContinuousFunctorRight HomTypeF :=
    fun _ _ _ _ _ =>
      pLim_lambda _ _ ∘ prepostcompose_cfun (fLeft _) (fRight _).

  Global Program Instance HomFunctorLeft :
    ContinuousFunctorLeft HomTypeF :=
    fun f _ _ _ _ =>
      (prepostcompose_cfun (fRight _) (fLeft _)) ∘ pLim_apply _ _.

  Global Program Instance HomContinuousFunctor
    : ContinuousFunctor HomTypeF.
  Next Obligation.
    unfold fLeft, fRight, HomFunctorLeft, HomFunctorRight.
    split; rewrite compose_cfun_assoc'; apply compose_cfun_iso;
      try apply pLim_lambda_apply_iso; apply prepostcompose_cfun_iso;
        try (destruct cFunc1; apply right_left_id);
        destruct cFunc2; apply right_left_id.
  Qed.
End homFunctor.
