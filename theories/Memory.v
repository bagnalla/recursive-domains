Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import Domains.Continuous Domains.Domain Domains.FunctorClasses
        Domains.Functors Domains.Order Domains.ProjectiveLimit.


(* Section store. *)
(*   Variable ptr : Type. *)
(*   Variable val : Type. *)
(*   Definition store := ptr -> val. *)
(* End store. *)

Section perm.
  Context ptr `{CPO ptr}.
  Context value `{CPO value}.

  Definition permF : TypeF :=
    fun X _ _ _ => ProductTypeF
                  (PERTypeF (ptr -> value))
                  (PreOrderTypeF (ptr -> value))
                  X _ _ _.

  (* The type of permissions. *)
  Definition perm := pLim (type_n permF).

  (* The recursive domain instance for permissions. *)
  Definition permDomain := ProjLimitRecursiveDomain permF.

  (* Aliases for the permission type fold and unfold operations. *)
  Definition permFold := Fold (pLim (type_n permF)).
  Definition permUnfold := Unfold (pLim (type_n permF)).

  (* (* OType instance for permissions. p1 ⊑ p2 whenever the PER and *)
  (*    preorder of p1 are subrelations of those of p2 at every n. *) *)
  (* Global Program Instance OTperm : OType perm := *)
  (*   {| oleq := fun p1 p2 => *)
  (*                forall n, match n with *)
  (*                     | O => True *)
  (*                     | S n' => fst (p1 (S n')) <o= fst (p2 (S n')) /\ *)
  (*                              snd (p1 (S n')) <o= snd (p2 (S n')) *)
  (*                     end |}. *)
  (* Next Obligation. *)
  (* split. *)
  (* - intros x []; auto; split; intros ? ? ?; auto. *)
  (* - intros x y z H1 H2 n. *)
  (*   specialize (H1 n); specialize (H2 n); destruct n; auto. *)
  (*   + destruct H1. destruct H2. split. *)
  (*     * intros ? ? ?; apply H2; apply H1; auto. *)
  (*     * intros ? ? ?; apply H4; apply H3; auto. *)
  (* Qed. *)

  (* Set Printing All. *)
  (* Print permUnfold. *)

  (* Program Definition cRelationEmpty A `{CPO A} : cRelation A := *)
  (*   const_cfun False. *)

  (* Program Definition cRelationFull A `{CPO A} : cRelation A := *)
  (*   const_cfun True. *)

  (* This isn't monotone... *)
  (* Program Definition cRelationRefl A `{CPO A} : cRelation A := *)
  (*   {| cfun_app := fun p => fst p =o= snd p|}. *)
  (* Admit Obligations. *)

  (* Program Definition unitPerm : perm := *)
  (*   fun n => match n with *)
  (*         | O => tt *)
  (*         | S n' => (_, _) *)
  (*         end. *)

  (* The least reflexive relation. *)
  Definition relationRefl A `{OType A} : relation A :=
    fun a b => a =o= b.

  (* Definition relationOrder A `{OType A} : relation A := *)
  (*   fun a b => a <o= b. *)

  (* Instance reflProper A `{OType A} : *)
  (*   Proper (oeq ==> oeq) (relationRefl A). *)
  (* Proof. *)
  (*   intros x y Heq; split; intros z ?; try rewrite Heq; auto; *)
  (*     rewrite <- Heq; auto. *)
  (* Qed. *)

  (* Instance orderProper A `{OType A} : *)
  (*   Proper (oeq ==> oleq ==> oleq) (relationOrder A). *)
  (* Proof. *)
  (*   intros x y Heq z w Hleq H2. *)
  (*   unfold relationOrder in *. *)
  (*   rewrite <- Heq. etransitivity; eauto. *)
  (* Qed. *)

  Instance reflProper A `{OType A} :
    Proper (oeq ==> oeq ==> oleq) (relationRefl A).
  Proof.
    intros ? ? Heq ? ? ? ?; rewrite <- Heq; etransitivity; eauto.
  Qed.

  (* Instance asdfOType A B {oA : OType A} {oB : OType B} (x : TypeWithCPO) *)
  (*   : OType ((A -> B) * ty_ty x) := *)
  (*   @OTpair _ _ (OTarrow A B) (ty_otype x). *)


  (* Let Coq find the OType instance form a TypeWithCPO. *)
  Instance TypeWithCPOOType (x : TypeWithCPO): OType (ty_ty x) :=
    ty_otype x.
  (* Instance TypeWithCPOSupremum (x : TypeWithCPO): Supremum (ty_ty x) := *)
  (*   ty_sup x. *)
  (* Instance TypeWithCPOCPO (x : TypeWithCPO): CPO (ty_ty x) := *)
  (*   ty_cpo x. *)

  (* The least reflexive relation is a PER. *)
  Lemma relationRefl_isPER A `{OType A} :
    isPER (relationRefl A).
  Proof.
    split; intros ?; try apply oeq_symm; auto; etransitivity; eauto.
  Qed.

  (* The least reflexive relation is a preorder. *)
  Lemma relationRefl_isPreOrder A `{OType A} :
    isPreOrder (relationRefl A).
  Proof.
    split.
    - intros ?; reflexivity.
    - split.
      + intros ?; etransitivity; eauto.
      + intros x y Heq1 z w Heq2 ?.
        rewrite <- Heq1. etransitivity; eauto.
  Qed.

  Lemma relationTotal_isPreOrder A `{OType A} :
    isPreOrder (fun _ _ => True).
  Proof. firstorder. Qed.

  (* The permission representing no permissions at all.*)
  Program Definition noPerm : perm :=
    fun n => match n with
          | O => tt
          | S n' => (fun _ _ => True, relationRefl _)
          end.
  Next Obligation. split; auto. Qed.
  Next Obligation. apply relationRefl_isPreOrder. Qed.
  (* Next Obligation. *)
  (*   destruct n; simpl. reflexivity.     *)
  (*   split. simpl. *)
  (*   split; simpl. *)
  (*   - intros x y _; auto. *)
  (*   - intros x y H1. unfold relationRefl in *. *)
  (*     split; simpl. split. *)
  (*     + intros z. destruct x, y. destruct H1 as [[] []]. simpl in *. *)
  (*       auto. *)
  (*     + split. *)
  (*       * admit. *)
  (*       * admit. *)
  (*     + split. *)
  (*       * intros z. destruct x, y. destruct H1 as [[] []]. simpl in *. *)
  (*         auto. *)
  (*       * admit. *)
  (*   - split; simpl. *)
  (*     + intros ? ? ?; auto. *)
  (*     + admit. *)
  (* Admitted. *)
  Admit Obligations.

  (* The permission representing full control over everything. *)
  Program Definition allPerm : perm :=
    fun n => match n with
          | O => tt
          | S n' => (relationRefl _, fun _ _ => True)
          end.
  Next Obligation. apply relationRefl_isPER. Qed.
  Next Obligation. apply relationTotal_isPreOrder. Qed.
  Admit Obligations.
End perm.


Section mem.
  Context ptr `{CPO ptr}.
  Context value `{CPO value}.

  Definition mem : Type := (ptr -> value) * (perm ptr value).
End mem.
