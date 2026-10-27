From CwFdeBruijn.Syntax.AKcf Require Export occur isref AKcf_Conv etaRelated.
From Stdlib Require Import Bool.

(* Definitions and reflections *)

Inductive Tmcfσvalue : Tmcf -> Prop :=
  | Tmcfσvalue_π₂ {δ : Tmscf} (Hδ : cf_iter_π₁idP δ)
    : Tmcfσvalue (Tmcf_π₂ δ)
  | Tmcfσvalue_app {x y: Tmcf} (Hx : Tmcfσvalue x) (Hy : Tmcfσvalue y)
    : Tmcfσvalue (Tmcf_app x y)
  | Tmcfσvalue_lam {x : Tmcf} (Hx : Tmcfσvalue x) : Tmcfσvalue (Tmcf_lam x).

Inductive Tmscfσvalue : Tmscf -> Prop :=
  | Tmscfσvalue_iterπ₁id {δ} (Hδ : cf_iter_π₁idP δ)
    : Tmscfσvalue δ
  | Tmscfσvalue_snoc {δ} (Hδ : Tmscfσvalue δ) {x} (Hx:Tmcfσvalue x)
      (Hη : ~ etaRelatedP δ x)
    : Tmscfσvalue (Tmscf_snoc δ x).

#[export] Hint Constructors cf_iter_π₁idP : AKcf.
#[export] Hint Constructors Tmcfσvalue : AKcf.
#[export] Hint Constructors Tmscfσvalue : AKcf.

Fixpoint Tmcfσvalueb (x: Tmcf) : bool :=
match x with
  | Tmcf_subst x δ => false
  | Tmcf_π₂ δ  => cf_iter_π₁idb δ
  | Tmcf_app x y => (Tmcfσvalueb x) && (Tmcfσvalueb y)
  | Tmcf_lam x => Tmcfσvalueb x
end.

Fixpoint Tmscfσvalueb (δ : Tmscf) : bool :=
match δ with
  | Tmscf_snoc δ x => Tmscfσvalueb δ && (Tmcfσvalueb x && negb (etaRelatedb δ x))
  | Tmscf_id => true
  | Tmscf_comp δ₁ δ₂ => false
  | Tmscf_π₁ δ => cf_iter_π₁idb δ
end.

Fixpoint Tmcfσvalue_spec (x: Tmcf) : reflect (Tmcfσvalue x) (Tmcfσvalueb x).
Proof.
  induction x.
  - apply ReflectF; intro; solve_by_invert.
  - simpl.
    refine (equivP (P := cf_iter_π₁idP δ) _ _).
    { apply cf_iter_π₁id_spec. }
    split.
    + apply Tmcfσvalue_π₂.
    + intro H; inversion H; assumption.
  - simpl.
    refine (equivP (P := (Tmcfσvalue x1) /\ (Tmcfσvalue x2)) _ _).
    { apply andPP; assumption. }
    split.
    + intros H; apply Tmcfσvalue_app; apply H.
    + intro H; inversion H; split; assumption.
  - simpl.
    refine (equivP (P := Tmcfσvalue x) _ _).
    { apply IHx. }
    split.
    + apply Tmcfσvalue_lam.
    + intro H; inversion H; assumption.
Qed.

Fixpoint Tmcfσvalue_rect
  (P : Tmcf -> Type)
  (X1 : forall δ : Tmscf, cf_iter_π₁idP δ -> P (Tmcf_π₂ δ))
  (X2 : forall x y : Tmcf, Tmcfσvalue x -> P x -> Tmcfσvalue y -> P y -> P (Tmcf_app x y))
  (X3 : forall x : Tmcf, Tmcfσvalue x -> P x -> P (Tmcf_lam x))
  (t : Tmcf) (H : Tmcfσvalue t) {struct t}
  : P t.
Proof.
  intros.
  assert (E := (proj1 (reflect_iff _ _ (Tmcfσvalue_spec t)) H)).
  induction t; simpl in E.
  - discriminate E.
  - apply X1.
    apply (reflect_iff _ _ (cf_iter_π₁id_spec δ)).
    exact E.
  - apply X2.
    + apply (reflect_iff _ _ (Tmcfσvalue_spec t1)).
      apply (andb_prop (Tmcfσvalueb t1) (Tmcfσvalueb t2)).
      exact E.
    + apply IHt1.
      * apply (reflect_iff _ _ (Tmcfσvalue_spec t1)).
        apply (andb_prop _ _ E).
      * apply (andb_prop _ _ E).
    + apply (reflect_iff _ _ (Tmcfσvalue_spec t2)).
      apply (andb_prop _ _ E).
    + apply IHt2.
      * apply (reflect_iff _ _ (Tmcfσvalue_spec t2)).
        apply (andb_prop _ _ E).
      * apply (andb_prop _ _ E).
  - apply X3.
    + apply (reflect_iff _ _ (Tmcfσvalue_spec t)).
      exact E.
    + apply IHt.
      * apply (reflect_iff _ _ (Tmcfσvalue_spec t)).
        exact E.
      * exact E.
Defined.

Lemma Tmscfσvalue_spec (δ: Tmscf) : reflect (Tmscfσvalue δ) (Tmscfσvalueb δ).
Proof.
  induction δ; simpl.
  + apply (equivP (P:=Tmscfσvalue δ /\ (Tmcfσvalue x /\ not (etaRelatedP δ x)))).
    - apply (andPP IHδ).
      apply (andPP (Tmcfσvalue_spec _)).
      apply negPP.
      apply etaRelated_spec.
    - split.
      * intros [Hδ [Hx Hη]].
        apply (Tmscfσvalue_snoc Hδ Hx).
        exact Hη.
      * intro H.
        inversion H; subst.
        -- exfalso; solve_by_invert.
        -- exact (conj Hδ (conj Hx Hη)).
  + apply ReflectT.
    apply Tmscfσvalue_iterπ₁id.
    apply cf_iter_π₁idP_id.
  + apply ReflectF.
    intro H; try solve_by_inverts 3.
  + apply (equivP (P:= cf_iter_π₁idP δ)).
    - apply cf_iter_π₁id_spec.
    - split.
      * intro H.
        auto with AKcf.
      * intro H.
        inversion H; subst; inversion Hδ; subst; assumption.
Qed.

Definition Tmscfσvalue_rect
  (P : Tmscf -> Type)
  (X1 : forall δ : Tmscf, cf_iter_π₁idP δ -> P δ)
  (X2 : forall δ : Tmscf, Tmscfσvalue δ -> P δ ->
        forall y : Tmcf, Tmcfσvalue y
          -> ~ etaRelatedP δ y
          -> P (Tmscf_snoc δ y))
  (δ : Tmscf) (H : Tmscfσvalue δ)
  : P δ.
Proof.
  assert (E := (proj1 (reflect_iff _ _ (Tmscfσvalue_spec δ)) H)).
  induction δ; simpl in E; try discriminate E.
  - destruct (andb_prop _ _ E) as [δV xV].
    apply X2.
    + apply (reflect_iff _ _ (Tmscfσvalue_spec δ)).
      exact δV.
    + apply IHδ.
      apply (reflect_iff _ _ (Tmscfσvalue_spec δ)).
      * exact δV.
      * exact δV.
    + apply (reflect_iff _ _ (Tmcfσvalue_spec x)).
      apply (andb_prop _ _ xV).
    + apply (elimN (etaRelated_spec δ x)).
      apply (andb_prop _ _ xV).
  - apply X1.
    repeat constructor.
  - apply X1.
    constructor.
    apply (reflect_iff _ _ (cf_iter_π₁id_spec δ)).
    exact E.
Defined.

Lemma Tmcfσvalue_dec (x: Tmcf) : {Tmcfσvalue x} + {not (Tmcfσvalue x)}.
Proof.
  apply (reflect_dec (Tmcfσvalue x) (Tmcfσvalueb x)).
  apply Tmcfσvalue_spec.
Qed.

Lemma Tmscfσvalue_dec (δ: Tmscf) : {Tmscfσvalue δ} + {not (Tmscfσvalue δ)}.
Proof.
  apply (reflect_dec (Tmscfσvalue δ) (Tmscfσvalueb δ)).
  apply Tmscfσvalue_spec.
Qed.

(* Lemmas *)

Lemma cf_appsubst_condition_decidability' {δ: Tmscf} (δV : Tmscfσvalue δ)
  : (forall y, δ <> (Tmscf_snoc Tmscf_id y)) + { y | (Tmcfσvalue y) /\ δ = Tmscf_snoc Tmscf_id y}.
Proof.
  induction δ.
  1:{ destruct δ.
    2:{
      right.
      split with x; split.
      - inversion δV; subst.
        + exfalso. try solve_by_invert.
        + assumption.
      - reflexivity.
    }
    all: left;
      discriminate.
  }
  all: left;
      discriminate.
Qed.

Lemma Tmcfσvalue_ref (i : nat) : Tmcfσvalue (Tmcf_ref i).
Proof.
  apply Tmcfσvalue_π₂.
  apply Tmscfσvalue_cf_iter_π₁id.
Qed.

Lemma Tmcfσvalue_ref' {x} (H : TmcfσisrefP x) : Tmcfσvalue x.
Proof.
  inversion H.
  apply Tmcfσvalue_π₂.
  exact Hδ.
Qed.

Lemma Tmscfσnf_id : normal_form Tmscfσstep (Tmscf_id).
Proof.
  intros [δ red].
  inversion red; subst.
  inversion H.
Qed.

Lemma Tmscfσnf_π₁id : normal_form Tmscfσstep (Tmscf_π₁ Tmscf_id).
Proof.
  intros [σ red].
  inversion red; subst.
  - inversion H.
  - inversion H0; subst.
    inversion H.
Qed.

Lemma Tmscfσnf_π₁π₁ {δ : Tmscf} (Hπ₁δ : normal_form Tmscfσstep (Tmscf_π₁ δ)) (Hδ : normal_form Tmscfσstep δ)
    : normal_form Tmscfσstep (Tmscf_π₁ (Tmscf_π₁ δ)).
Proof.
  intros [σ red].
  inversion red; subst.
  - inversion H.
  - inversion H0; subst.
    + inversion H; subst.
      apply Hπ₁δ.
      esplit.
      apply cf_srefl.
      apply cf_π₁beta.
    + apply Hδ.
      esplit.
      apply H1.
Qed.

Lemma Tmcfσnf_cf_iter_π₁id (i : nat) : normal_form Tmscfσstep (cf_iter_π₁ i Tmscf_id).
Proof.
  induction i as [i IHi] using lt_wf_ind.
  induction i as [| [ | i] _ ].
  { exact Tmscfσnf_id. }
  { exact Tmscfσnf_π₁id. }
  simpl.
  apply Tmscfσnf_π₁π₁.
  + apply (IHi (S i)).
    lia.
  + apply (IHi i).
    lia.
Qed.

Lemma cf_iter_π₁idP_is_nf (δ: Tmscf) : cf_iter_π₁idP δ -> normal_form Tmscfσstep δ.
Proof.
  intro H.
  destruct (cf_iter_π₁idP_to_cf_iter_π₁id H); subst.
  apply Tmcfσnf_cf_iter_π₁id.
Qed.

Lemma Tmcf_ref_nf i : normal_form Tmcfσstep (Tmcf_ref i).
Proof.
  induction i; intros [x abs].
  - inversion abs; subst; try solve_by_inverts 2.
  - inversion abs; subst; try solve_by_invert.
  inversion H0; subst.
  * inversion H; subst; induction i; discriminate H2.
  * eapply IHi.
    esplit.
    apply (cf_π₂_prpg _ _ H1).
Qed.

Lemma Tmscfσ_comp_progress (δ σ : Tmscf): exists ν, (Tmscf_comp δ σ) --s> ν.
Proof.
  destruct δ; esplit; apply cf_srefl; auto with AKcf.
Qed.

(* Value iff Normal form *)

Theorem Tmcfσvalue_is_nf (x: Tmcf) : Tmcfσvalue x -> normal_form Tmcfσstep x.
Proof.
  intro H.
  induction H.
  - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [i ?]; subst.
    apply Tmcf_ref_nf.
  - intros [z red].
    inversion red; subst; try solve_by_invert.
    + apply IHTmcfσvalue1.
      esplit.
      exact H4.
    + apply IHTmcfσvalue2.
      esplit.
      exact H4.
  - intros [z red].
    inversion red; subst; try solve_by_invert.
    apply IHTmcfσvalue.
    esplit.
    exact H1.
Qed.

Theorem Tmscfσvalue_is_nf (δ : Tmscf) (H : Tmscfσvalue δ) : normal_form Tmscfσstep δ.
Proof.
  induction H as [δ Hδ | δ Hδ IHδ y Hy].
  - apply (cf_iter_π₁idP_is_nf _ Hδ).
  - intros [z abs].
    inversion abs; subst.
    + inversion H; subst.
      apply Hη.
      constructor.
    + apply IHδ.
      esplit.
      exact H2.
    + apply (Tmcfσvalue_is_nf y Hy).
      esplit.
      exact H2.
Qed.

Fixpoint Tmcfσnf_strong_progress (x : Tmcf) : (Tmcfσvalue x) \/ (exists x', (x --> x')%AKcf).
Proof.
  induction x.
  - destruct IHx as [xV | xR].
    2: {
      destruct xR as [x' xred].
      right.
      esplit.
      apply subst_Tmcf_prpg.
      apply xred.
    }
    { induction xV.
      all: right;esplit;apply cf_refl.
      + apply cf_substπ₂.
      + apply cf_appsubst.
      + apply cf_lamsubst.
    }
  - induction δ.
    + right;esplit;apply cf_refl. apply cf_π₂beta.
    + left. apply Tmcfσvalue_π₂. apply cf_iter_π₁idP_id.
    + destruct (Tmscfσ_comp_progress δ1 δ2) as [? cred].
      right;esplit; apply cf_π₂_prpg; apply cred.
    + destruct IHδ as [π₂δV | [y π₂δred]].
      * inversion π₂δV; subst.
        left.
        apply Tmcfσvalue_π₂.
        apply cf_iter_π₁idP_π₁.
        exact Hδ.
      * right.
        inversion π₂δred; subst.
        --inversion H; subst.
          esplit.
          apply cf_π₂_prpg.
          apply cf_srefl.
          apply cf_π₁beta.
        --esplit.
          apply cf_π₂_prpg.
          apply cf_π₁_prpg.
          exact H0.
  - destruct IHx1 as [x1V | [x1' x1red]].
    + destruct IHx2 as [x2V | [x2' x2red]].
      * left.
        apply Tmcfσvalue_app; assumption.
      * right. esplit. apply cf_rator_prpg. apply x2red.
    + right. esplit. apply cf_rand_prpg. apply x1red.
  - destruct IHx as [xV | [x' xred]].
    + left.
      apply Tmcfσvalue_lam.
      exact xV.
    + right.
      esplit.
      apply cf_lam_prpg.
      exact xred.
Qed.

Lemma Tmcfσnf_is_value {x: Tmcf} : normal_form Tmcfσstep x -> Tmcfσvalue x.
Proof.
  intro H.
  destruct (Tmcfσnf_strong_progress x) as [xV |xred].
  + exact xV.
  + exfalso.
    apply H.
    exact xred.
Qed.

Lemma Tmscfσnf_strong_progress (δ : Tmscf) : (Tmscfσvalue δ) \/ (exists δ', (δ --s> δ')%AKcf).
Proof.
  induction δ.
  - destruct IHδ as [δV | [σ δred]].
    + destruct (Tmcfσnf_strong_progress x) as [xV | [y xred]].
      * destruct (reflect_dec _ _ (etaRelated_spec δ x)).
        --right.
          destruct e.
          esplit.
          subst.
          apply cf_srefl.
          apply cf_πeta.
        --left.
          apply (Tmscfσvalue_snoc δV xV).
          exact n.
      * right.
        esplit.
        apply snoc_Tmcf_prpg.
        exact xred.
    + right.
      esplit.
      apply snoc_Tmscf_prpg.
      exact δred.
  - left.
    apply Tmscfσvalue_iterπ₁id.
    apply cf_iter_π₁idP_id.
  - destruct (Tmscfσ_comp_progress δ1 δ2) as [? cred].
    right.
    esplit.
    apply cred.
  - destruct IHδ as [δv | [? δred]].
    + induction δv.
      * left.
        apply Tmscfσvalue_iterπ₁id.
        apply cf_iter_π₁idP_π₁.
        assumption.
      * right.
        esplit.
        apply cf_srefl.
        apply cf_π₁beta.
    + right.
      esplit.
      apply cf_π₁_prpg.
      exact δred.
Qed.

Lemma Tmscfσnf_is_value (δ: Tmscf) : normal_form Tmscfσstep δ -> Tmscfσvalue δ.
Proof.
    intro H.
  destruct (Tmscfσnf_strong_progress δ) as [δV |δred].
  + exact δV.
  + exfalso.
    apply H.
    exact δred.
Qed.