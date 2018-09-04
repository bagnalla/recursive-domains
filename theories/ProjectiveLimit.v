Require Import Domains.Continuous Domains.Domain Domains.EPPair
        Domains.Order.

Definition pLim f `{EPChain f} : Type :=
  { s : forall n, f n | forall n, s n =o= (proj (chain n)) @c@ (s (S n)) }.

(* Ordered type for EPChain suprema. *)
Instance OTpLim {f g h i} (G : @EPChain f g h i) : OType (pLim f) :=
  {| oleq := fun s1 s2 => forall n, @oleq (f n) (g n) (val s1 n) (val s2 n) |}.
Proof.
  constructor.
  - intros ?; reflexivity.
  - intros ?; etransitivity; eauto.
Defined.

Program Definition supChainNth {f g h i} (epChain : @EPChain f g h i)
        (A : @omegaChain (pLim f) _)
        (n : nat) : @omegaChain (f n) (g n) :=
  fun j => proj1_sig A j n.
Next Obligation. intros j; destruct A; simpl; firstorder. Qed.

Program Instance PLimSupremum {f g h i} (epChain : @EPChain f g h i)
  : Supremum (pLim f) := fun A => fun n => (h n) (supChainNth epChain A n).
Next Obligation.
  destruct (chain n) as [? proj]  eqn:Hchain;
    destruct proj as [proj ? Hprojcont]; simpl in *.
  pose proof Hprojcont as Hcont.
  specialize (Hcont (supChainNth epChain A (S n))); rewrite Hcont.
  pose proof i as Hcpo; specialize (Hcpo n); destruct Hcpo.
  apply Proper_oleq_oeq; split; intros j; destruct A; simpl in *;
    destruct (x j); rewrite (o0 n); rewrite Hchain; reflexivity.
Qed.

Program Instance PLimCPO {f g h i} (epChain : @EPChain f g h i)
  : CPO (pLim f).
Next Obligation.
  split.
  - intros ? n.
    pose proof i as Hcpo; specialize (Hcpo n); destruct Hcpo as [ax _].
    destruct (ax (supChainNth epChain A n)) as [H _]; apply H.
  - intros b Hub n.
    pose proof i as Hcpo; specialize (Hcpo n); destruct Hcpo as [ax _].
    destruct (ax (supChainNth epChain A n)) as [_ H]; apply H.
    intros ?; destruct b; apply Hub.
Qed.
Next Obligation.
  intros x y Heq; intros n; pose proof i as Hcpo;
    specialize (Hcpo n); destruct Hcpo; apply supremumProper;
      intros j; try apply H0; apply Heq.
Qed.


Section cone.
  (* A cone from A to the diagram G (technically indexed by nat^op). *)
  Record Cone (A : Type) f `{CPO A} `{EPChain f} : Type :=
    { cone : forall n, A -c> (f n)
    ; cone_pf : forall n x, (cone n @c@ x) =o=
                       proj (chain n) @c@ (cone (S n) @c@ x)
    }.

  Arguments cone {_ _ _ _ _ _ _ _ _}.

  Program Definition cone_id f `{EPChain f}
    : Cone (pLim f) f :=
    {| cone := fun n => {| cfun_app := fun f => f n |} |}.
  Next Obligation. firstorder. Qed.
  Next Obligation.
    destruct (i n) as [_ ?]; apply Proper_oleq_oeq; split; simpl; reflexivity.
  Qed.
  Next Obligation. destruct x; auto. Qed.

  Program Definition compose_cone {A B} `{CPO A} `{CPO B} {f} `{EPChain f}
          (g : A -c> B) (mu : Cone B f) : Cone A f :=
    {| cone := fun n => compose_cfun g (cone mu n) |}.
  Next Obligation. destruct mu; auto. Qed.

  Program Definition product_cone {A B} `{CPO A} `{CPO B}
          {f1 f2} `{EPChain f1} `{EPChain f2}
          (C1 : Cone A f1) (C2 : Cone B f2)
    : Cone (A*B) (ProductTypeSequence f1 f2) :=
    {| cone := fun n => pair_cfun (cone C1 n) (cone C2 n) |}.
  Next Obligation.
    destruct C1; destruct C2; apply Proper_pair; auto.
  Qed.

  Program Definition proj1_cone {A B} `{CPO A} `{CPO B}
          {f1 f2} `{EPChain f1} `{EPChain f2}
          (C : Cone A (ProductTypeSequence f1 f2)) : Cone A f1 :=
    {| cone := fun n => fst_cfun ∘ (cone C n) |}.
  Next Obligation.
    destruct C; simpl; specialize (cone_pf0 n x).
    destruct (cone0 n), (cone0 (S n)); simpl in *;
      destruct (cfun_app0 x); firstorder.
  Qed.

  Program Definition proj2_cone {A B} `{CPO A} `{CPO B}
          {f1 f2} `{EPChain f1} `{EPChain f2}
          (C : Cone A (ProductTypeSequence f1 f2)) : Cone A f2 :=
    {| cone := fun n => snd_cfun ∘ (cone C n) |}.
  Next Obligation.
    destruct C; simpl; specialize (cone_pf0 n x).
    destruct (cone0 n), (cone0 (S n)); simpl in *;
      destruct (cfun_app0 x); firstorder.
  Qed.

  Program Definition pLim_intro {A} `{CPO A} {f} `{EPChain f} (C : Cone A f)
    : (A -c> pLim f) :=
    {| cfun_app := fun x => fun n => cone C n @c@ x |}.
  Next Obligation. destruct C; simpl; apply cone_pf0. Qed.
  Next Obligation.
    intros x y Hleq n. simpl.
    destruct C. simpl. destruct (cone0 n). simpl.
    rewrite Hleq. reflexivity.
  Qed.
  Next Obligation.
    destruct C; split; simpl; intros n; destruct (cone0 n) eqn:Hconen;
      destruct (cfun_Continuous A0); etransitivity; eauto;
        destruct (i n); apply supremumProper; intros m; simpl;
          rewrite Hconen; reflexivity.
  Qed.

  Program Definition pLim_proj f `{EPChain f} n
    : pLim f -c> f n :=
    {| cfun_app := fun f => f n |}.
  Next Obligation. intros ? ? ?; auto. Qed.
  Next Obligation.
    destruct (i n); apply Proper_oleq_oeq; split; simpl; reflexivity.
  Qed.

  Lemma pLim_product_sound f1 f2 `{G1 : EPChain f1} `{G2 : EPChain f2} :
    (pLim_intro (product_cone (cone_id f1) (cone_id f2)))
      ∘ tuple_cfun
      (pLim_intro (proj1_cone (cone_id (ProductTypeSequence f1 f2))))
      (pLim_intro (proj2_cone (cone_id (ProductTypeSequence f1 f2))))
    =o= id_cfun _.
  Proof. split; intros [] []; firstorder. Qed.

  Lemma pLim_product_complete f1 f2 `{G1 : EPChain f1} `{G2 : EPChain f2} :
    tuple_cfun
      (pLim_intro (proj1_cone (cone_id (ProductTypeSequence f1 f2))))
      (pLim_intro (proj2_cone (cone_id (ProductTypeSequence f1 f2))))
      ∘ pLim_intro (product_cone (cone_id f1) (cone_id f2))
    =o= id_cfun _.
  Proof. split; intros [] []; firstorder. Qed.

  Program Definition pLim_const_lambda T `{CPO T} f `{EPChain f}
    : (T -> pLim f) -c> pLim (ConstHomTypeSequence T f) :=
    {| cfun_app := fun f n x => f x n |}.
  Next Obligation.
    split; simpl; intros x; destruct (f x); simpl; firstorder.
  Qed.
  Next Obligation. intros ? ? Hleq ? ?; apply Hleq. Qed.
  Next Obligation.
    split; simpl; intros n ?; destruct (i n) as [? supProp];
      apply supProp; simpl; reflexivity.
  Qed.

  Program Definition pLim_const_apply T `{CPO T} f `{EPChain f}
    : pLim (ConstHomTypeSequence T f) -c> (T -> pLim f) :=
  {| cfun_app := fun f x n => f n x |}.
  Next Obligation. destruct f; simpl; firstorder. Qed.
  Next Obligation. intros ? ? Hleq ? ?; apply Hleq. Qed.
  Next Obligation.
    split; simpl; intros ? n; destruct (i n) as [? supProp];
      apply supProp; simpl; reflexivity.
  Qed.

  Lemma pLim_const_lambda_apply_iso T `{CPO T} f `{EPChain f} :
    isomorphism (pLim_const_lambda T f) (pLim_const_apply T f).
  Proof. split; split; intros ? ? Hleq1; apply Hleq1; auto. Qed.

  (* Program Definition mkPLim {f} `{EPChain f} {n} (x : f n) : pLim f := _. *)
  (* Admit Obligations. *)

  (* Lemma mkPLim_sound {f} `{EPChain f} {n} (x : f n) : *)
  (*   val (mkPLim x) n =o= x. *)
  (* Admitted. *)

  (* Lemma mkPLim_le f `{EPChain f} n m (G : pLim f) : *)
  (*   val (mkPLim (val G n)) m <o= val G m. *)
  (* Admitted. *)

  (* Program Definition pLim_lambda f1 f2 `{EPChain f1} `{EPChain f2} *)
  (*   : (pLim f1 -c> pLim f2) -c> pLim (HomTypeSequence f1 f2) := *)
  (*   {| cfun_app := *)
  (*        fun f => *)
  (*          fun n => *)
  (*            {| cfun_app := *)
  (*                 fun x => (f @c@ mkPLim x) n  |} |}. *)
  (* Admit Obligations. *)

  (* Program Definition pLim_apply f1 f2 `{EPChain f1} `{EPChain f2} *)
  (*   : pLim (HomTypeSequence f1 f2) -c> (pLim f1 -c> pLim f2) := *)
  (*   {| cfun_app := *)
  (*        fun f => *)
  (*          {| cfun_app := *)
  (*               fun g => *)
  (*                 fun n => f n @c@ g n |} |}. *)
  (* Admit Obligations. *)

  (* (* This may not hold in general. Apply after lambda only composes to *) *)
  (* (*    identity if the function f is proper in a sense. The nth *) *)
  (* (*    component of the output of f should be a function only of the nth *) *)
  (* (*    component of the input. *) *)
  (* Lemma pLim_lambda_apply_iso f1 f2 `{EPChain f1} `{EPChain f2} : *)
  (*   isomorphism (pLim_lambda f1 f2) (pLim_apply f1 f2). *)
  (* Proof. *)
  (*   split. *)
  (*   - split; simpl. *)
  (*     + intros f' g' Hleq1 x y Hleq2 n. *)
  (*       apply Hleq1. *)
  (*       intros m. *)
  (*       etransitivity; auto. *)
  (*       apply mkPLim_le. *)
  (*     + intros f' g' Hleq1 x y Hleq2 n. *)
  (*       apply Hleq1. *)
  (*       intros m.         *)
  (*       etransitivity; auto. *)
  (*       apply mkPLim_le. *)
  (*     +  *)
  (* Admitted. *)

  (* Lemma pLim_lambda_apply_iso_1 f1 f2 `{EPChain f1} `{EPChain f2} f : *)
  (*   pLim_lambda f1 f2 @c@ (pLim_apply f1 f2 @c@ f) =o= f. *)
  (* Proof. *)
  (*   split; simpl; intros n x y Hleq; destruct f as [f ?]; simpl; *)
  (*     destruct (f n) as [fn fProp ?]; apply fProp; *)
  (*       rewrite mkPLim_sound; apply Hleq. *)
  (* Qed. *)

  (* Lemma iso_1 {A B : Type} `{CPO A} `{CPO B} (f : A -c> B) (g : B -c> A) : *)
  (*     (forall x, g @c@ (f @c@ x) =o= x) -> *)
  (*     g ∘ f =o= id_cfun _. *)
  (* Proof. *)
  (*   intros H1; split; simpl. *)
  (*   - intros x y Hleq. transitivity (g @c@ (f @c@ y)). *)
  (*     + destruct f, g; rewrite Hleq; reflexivity. *)
  (*     + apply H1. *)
  (*   - intros x y Hleq. etransitivity. *)
  (*     + apply Hleq. *)
  (*     + apply H1. *)
  (* Qed. *)

  (* (* Need the additional property of f. *) *)
  (* (* This probably isn't the right way to express it. Maybe something *) *)
  (* (*    like: forall g n, exists f', f g n =o= f' (g n). Basically just *) *)
  (* (*    that the nth component of f g is a function of the nth component *) *)
  (* (*    of g. *) *)
  (* Lemma pLim_lambda_apply_iso_2 f1 f2 `{EPChain f1} `{EPChain f2} *)
  (*       (f : pLim f1 -c> pLim f2) : *)
  (*   (forall (x : pLim f1) n, *)
  (*       val (f @c@ (mkPLim (val x n))) n =o= val (f @c@ x) n) -> *)
  (*   pLim_apply f1 f2 @c@ (pLim_lambda f1 f2 @c@ f) =o= f. *)
  (* Proof. *)
  (*   intros Hf; split; simpl. *)
  (*   - intros x y Hleq n. *)
  (*     destruct f as [f ?]. simpl. *)
  (*     transitivity (val (f x) n). *)
  (*     + apply Hf. *)
  (*     + apply cfun_Proper0. simpl. apply Hleq. *)
  (*   - intros x y Hleq n. *)
  (*     transitivity (val (f @c@ y) n). *)
  (*     + destruct f. simpl. *)
  (*       apply cfun_Proper0. simpl. apply Hleq. *)
  (*     + apply Hf. *)
  (* Qed. *)

  (** Admit these for now... *)
  Program Definition pLim_lambda f1 f2 `{EPChain f1} `{EPChain f2}
    : (pLim f1 -c> pLim f2) -c> pLim (HomTypeSequence f1 f2).
  Admitted.
  Program Definition pLim_apply f1 f2 `{EPChain f1} `{EPChain f2}
    : pLim (HomTypeSequence f1 f2) -c> (pLim f1 -c> pLim f2).
  Admitted.
  Lemma pLim_lambda_apply_iso f1 f2 `{EPChain f1} `{EPChain f2} :
    isomorphism (pLim_lambda f1 f2) (pLim_apply f1 f2).
  Admitted.
End cone.


(* Section productPLim. *)
(*   Context f1 `{G1 : EPChain f1} f2 `{G2 : EPChain f2}. *)

(*   Program Definition productPLimFold : *)
(*     pLim f1 * pLim f2 -c> pLim (ProductTypeSequence f1 f2) := *)
(*     {| cfun_app := fun p => fun n => (fst p n, snd p n) |}. *)
(*   Admit Obligations. *)

(*   Program Definition productPLimUnfold : *)
(*     pLim (ProductTypeSequence f1 f2) -c> pLim f1 * pLim f2 := *)
(*     {| cfun_app := fun h => (fun n => fst (h n), fun n => snd (h n)) |}. *)
(*   Admit Obligations. *)

(*   Lemma productPLimIsomorphism : *)
(*     isomorphism productPLimFold productPLimUnfold. *)
(*   Proof. split; split; simpl; auto. Qed. *)
(* End productPLim. *)


Section productPLim.
  Context (T : Type) {oT : OType T} {supT : Supremum T} {cpoT : CPO T}.
  Context f1 `{G1 : EPChain f1} f2 `{G2 : EPChain f2}.

  Program Definition productPLimFold :
    (T * pLim f1) * (T * pLim f2) -c>
    pLim (ProductTypeSequence
            (ProductTypeSequence (ConstTypeSequence T) f1)
            (ProductTypeSequence (ConstTypeSequence T) f2)) :=
    {| cfun_app := fun p => fun n =>
                           ((fst (fst p), snd (fst p) n),
                            (fst (snd p), snd (snd p) n)) |}.
  Admit Obligations.

  Program Definition productPLimUnfold :
    pLim (ProductTypeSequence
            (ProductTypeSequence (ConstTypeSequence T) f1)
            (ProductTypeSequence (ConstTypeSequence T) f2)) -c>
    (T * pLim f1) * (T * pLim f2) :=
    {| cfun_app := fun h => ((fst (fst (h 0)), fun n => snd (fst (h n))),
                          (fst (snd (h 0)), fun n => snd (snd (h n)))) |}.
  Admit Obligations.

  Lemma productPLimIsomorphism :
    isomorphism productPLimFold productPLimUnfold.
  Proof. 
    simpl.
    split.
    - split; simpl; intros [[] []] [[] []] [[] []]; split; auto.
    - split; simpl.
      + intros x y H n.
        destruct x, y. simpl in *.
        specialize (H n). destruct H as [[] []].
        split; split; auto.
        * etransitivity. shelve. apply H.
          Unshelve.
          clear H H0 H1 H2.
          induction n. reflexivity.
          specialize (o n).
          destruct o as [[[? _] _] _].
          etransitivity. apply IHn. destruct (x (S n)). simpl in *.
          destruct p. simpl in *. auto.
        (* TODO: clean this step up. The 3 admits are the same proof. *)
        * admit.
      + intros x y H n.
        destruct x, y. simpl in *.
        specialize (H n). destruct H as [[] []].
        split; split; auto.
        * admit.
        * admit.
  Admitted.
End productPLim.
