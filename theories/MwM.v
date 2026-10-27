From Stdlib Require Import ssrfun Nat PeanoNat Lia.
From Category Require Import Lib Theory Theory.Morphisms.
From Category.Functor Require Import Hom.
#[warnings="-notation-incompatible-prefix"]
From Category.Instance Require Import 
  Sets Sets.Cartesian Fun Fun.Cartesian.
From Category Require Import Construction.Subcategory.
From CwFdeBruijn.Lib Require Import Transport.
From CwFdeBruijn Require Import CatPsh Uwcwf Structure.Uwcwf Structure.Uwcwf.Lift FullSubCategory.

Section definitions.

  Context {C : UWCwF}.

  Class MonoidWithModule : Prop := 
  {
    hasSingleContext : forall c : ctx C, c = ⋆__;
  }.
  
End definitions.
Arguments hasSingleContext _ : clear implicits.

Definition MwM := { C : UWCwF & @MonoidWithModule C }.
Definition MwM_incl : MwM -> UWCwF
  := @projT1 UWCwF (@MonoidWithModule).
Coercion MwM_incl : MwM >-> UWCwF.
#[global]
Instance MwM_MonoidWithModule (C : MwM) : @MonoidWithModule C
  := projT2 C.
Arguments MonoidWithModule _ : clear implicits.

Definition MwMs : Category := Sub _ (make_FullSubCategory UWCwFs MonoidWithModule).

Section transport.
  Context {M : MwM}.

  Definition MwM_contraction := (fun x:M => eq_sym (hasSingleContext M _ x)).

  Definition MwM_prop : forall x y:M, x = y := contraction_to_prop _ MwM_contraction.

  Definition MwM_CtxUIP (m:M) (p:m=m) : p = erefl
    := contractible_eq_refl (⋆_M) MwM_contraction p.

  Definition MwM_transport_to_exttgt {m} (δ : m ~> ⋆_M)
    := homcast erefl (eq_sym (hasSingleContext _ _ (s (⋆_M)))) δ.
  Definition MwM_transport_from_exttgt {m} (δ : m ~> s (⋆_M))
    := homcast erefl (hasSingleContext _ _ (s (⋆_M))) δ.
  Definition MwM_transport_from_extsrc {m} (δ : s (⋆_M) ~> m)
    := homcast (hasSingleContext _ _ (s (⋆_M))) erefl δ.

  Lemma MwM_transport_to_from_tgt {m} (δ : m ~> s (⋆_M)) : (MwM_transport_to_exttgt (MwM_transport_from_exttgt δ)) = δ.
  Proof.
    unfold MwM_transport_to_exttgt, MwM_transport_from_exttgt.
    rewrite homcast_trans.
    apply (homcast_UIP MwM_CtxUIP).
  Qed.
End transport.

Section Accessors.
  Context {M : MwM}.

  Definition MwM_S : Type := (⋆_M) ~> (⋆_M).
  #[global]
  Instance MwM_S_Setoid :
  Setoid (MwM_S) := {
    equiv := equiv
  }.

  Definition MwM_T : Type := @Tm M (⋆_M).
  #[global]
  Instance MwM_T_Setoid :
  Setoid (MwM_T) := {
    equiv := equiv
  }.

  Definition MwM_pi1 (δ : MwM_S) : MwM_S
    := π1 (MwM_transport_to_exttgt δ).
  #[global] Instance proper_MwM_pi1
    : (Proper (equiv ==> equiv) (MwM_pi1 )).
  Proof.
    intros ? ? E.
    unfold MwM_pi1.
    now rewrite E.
  Qed.

  Definition MwM_pi2 (δ : MwM_S) : MwM_T
    := π2 (MwM_transport_to_exttgt δ).
  #[global] Instance proper_MwM_pi2
    : (Proper (equiv ==> equiv) (MwM_pi2 )).
  Proof.
    intros ? ? E.
    unfold MwM_pi2.
    now rewrite E.
  Qed.

  Definition MwM_snoc (δ : MwM_S) (a:MwM_T) : MwM_S
    := MwM_transport_from_exttgt (snoc δ a).
  #[global] Instance proper_MwM_snoc
    : (Proper (equiv ==> equiv ==> equiv) (MwM_snoc )).
  Proof.
    intros ? ? Eδ ? ? Ea.
    unfold MwM_snoc.
    now rewrite Eδ, Ea.
  Qed.

  Definition MwM_subst (a:MwM_T) (δ : MwM_S)  : MwM_T
    := subst a (δ : ⋆__ ~{M}~> ⋆__).
  #[global] Instance proper_MwM_subst
    : (Proper (equiv ==> equiv ==> equiv) (MwM_subst )).
  Proof.
    intros ? ? Ea ? ? Eδ.
    unfold MwM_subst.
    now rewrite Eδ, Ea.
  Qed.

  Definition MwM_Lift : M ~{CwPs}~> M := @Lift M.

  Definition MwM_lift_on_sbs (δ : MwM_S) : MwM_S
    := MwM_transport_from_extsrc (MwM_transport_from_exttgt (fsbs[MwM_Lift] δ)).
  #[global] Instance proper_MwM_lift_on_sbs
    : (Proper (equiv ==> equiv) (MwM_lift_on_sbs)).
  Proof.
    intros ? ? Eδ.
    unfold MwM_lift_on_sbs.
    now rewrite Eδ.
  Qed.

End Accessors.

Section Properties.
  Lemma MwM_pi1_snoc {M:MwM} (δ : @MwM_S M) (a : MwM_T)
    : MwM_pi1 (MwM_snoc δ a) ≈ δ.
  Proof.
    unfold MwM_pi1, MwM_snoc.
    simpl.
    rewrite MwM_transport_to_from_tgt.
    refine (pi1_snoc M δ a).
  Qed.

  Lemma MwM_pi2_snoc {M:MwM} (δ : @MwM_S M) (a : MwM_T)
    : MwM_pi2 (MwM_snoc δ a) ≈ a.
  Proof.
    unfold MwM_pi2, MwM_snoc.
    rewrite MwM_transport_to_from_tgt.
    refine (pi2_snoc M δ a).
  Qed.

  Lemma MwM_snoc_eta {M:MwM} (δ : @MwM_S M)
    : δ ≈ MwM_snoc (MwM_pi1 δ) (MwM_pi2 δ).
  Proof.
    unfold MwM_pi1, MwM_pi2, MwM_snoc.
    apply homcast_adj.
    refine (@snoc_eta M _ _ _).
  Qed.

  Lemma MwM_pi1_comp {M:MwM} (γ δ : @MwM_S M)
  : (MwM_pi1 δ) ∘ γ ≈ MwM_pi1 (δ ∘ γ).
  Proof.
    unshelve etransitivity.
    { exact (MwM_pi1 δ ∘ (homcast erefl erefl γ)). }
    { reflexivity. }
    unfold MwM_pi1.
    etransitivity; [refine (@pi1_comp M _ _ _ _ _)|].
    unfold MwM_transport_to_exttgt.
    now rewrite <-homcast_comp.
  Qed.
  Lemma MwM_pi1_id_comp {M:MwM} (δ : @MwM_S M)
  : (MwM_pi1 id) ∘ δ ≈ MwM_pi1 δ.
  Proof.
    rewrite MwM_pi1_comp.
    cat.
  Qed.

  Lemma MwM_iterpi1_id_comp {M:MwM} (i:nat) (δ : @MwM_S M)
  : (iter i MwM_pi1 id) ∘ δ ≈ iter i MwM_pi1 δ.
  Proof.
    revert δ; induction i; intros δ.
    { simpl. cat. }
    
    rewrite Nat.iter_succ, MwM_pi1_comp.
    rewrite (IHi δ).
    reflexivity.
  Qed.

  Lemma MwM_iterpi1_itersnoc {M:MwM} (i:nat) (δ : @MwM_S M) (a : @MwM_T M)
  : iter i MwM_pi1 (iter i (MwM_snoc^~ a) δ) ≈ δ.
  Proof.
    revert δ; induction i; intros δ.
    { simpl. cat. }
    
    rewrite (Nat.iter_succ_r _ _ (MwM_snoc^~ a) _).
    rewrite Nat.iter_succ.
    rewrite (IHi (MwM_snoc δ a)).
    rewrite MwM_pi1_snoc.
    reflexivity.
  Qed.

  Lemma MwM_pi1id_epic {M:MwM} : Epic (MwM_pi1 id{M}).
  Proof.
    unfold MwM_pi1, MwM_transport_to_exttgt.
    destruct (hasSingleContext _ (MwM_MonoidWithModule M) (s (⋆_ _))).
    simpl.
    refine (@π1id_epic M (⋆__) _).
    exact (MwM_pi2 id).
  Qed.

  Lemma MwM_iterpi1id_epic {M:MwM} (i:nat) : Epic (iter i MwM_pi1 id{M}).
  Proof.
    induction i.
    { apply id_epic. }
    simpl.
    constructor; intros o.
    rewrite (hasSingleContext _ _ o).
    intros γ δ E.
    rewrite <-MwM_pi1_id_comp, !comp_assoc in E.
    apply MwM_pi1id_epic.
    apply IHi.
    exact E.
  Qed.

  Lemma MwM_pi2_subst {M:MwM} (γ δ : @MwM_S M)
    : MwM_subst (MwM_pi2 γ) δ ≈ MwM_pi2 (γ ∘ δ).
  Proof.
    unshelve etransitivity.
    { exact (MwM_subst (MwM_pi2 γ) (homcast erefl erefl δ)). }
    { reflexivity. }
    unfold MwM_pi2.
    etransitivity; [refine (pi2_subst _ _ _)|].
    unfold MwM_transport_to_exttgt.
    now rewrite <-homcast_comp.
  Qed.

  Lemma MwM_pi2id_subst {M:MwM} (δ : @MwM_S M)
    : MwM_subst (MwM_pi2 id) δ ≈ MwM_pi2 δ.
  Proof.
    rewrite MwM_pi2_subst, id_left.
    reflexivity.
  Qed.
End Properties.

Section induction.

  Context {M : MwM}.

  Definition MwM_ind (P : ctx M -> Type)
    (f0 : P (⋆_ ctx M))
    :forall (m :ctx M), P m .
  Proof.
    intro m.
    apply (Logic.transport _ (MwM_contraction m) f0).
  Defined.

End induction.