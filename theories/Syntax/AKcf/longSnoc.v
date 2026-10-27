From CwFdeBruijn.Syntax.AKcf Require Import AKcf AKcf_Conv Conv_Lemmas GenRewr.
Require Import Setoid Morphisms RelationClasses.
From Stdlib Require Import ssrfun.

#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Vectors.Vector.
Import Vectors.Vector.VectorNotations.

Open Scope AKcf.

Fixpoint AKcf_longsnoc {n} (δ : Tmscf) (v : Vector.t Tmcf n) : Tmscf
:= match v with
| [] => δ
| t :: ts => Tmscf_snoc (AKcf_longsnoc δ ts) t (* Note: v gets visually flipped*)
end.

Section Compatibility.

Definition Tmcfvecσstep {n : nat} : relation (Vector.t Tmcf n) := Vector.Forall2 Tmcfσstep.
Definition Tmcfvecσconv {n : nat} : relation (Vector.t Tmcf n) := Vector.Forall2 Tmcfσconv.
Definition Tmcfvecσeq {n : nat} : relation (Vector.t Tmcf n) := Vector.Forall2 Tmcfσeq.

Global Instance Tmcfvecσconv_preorder {n} : PreOrder (@Tmcfvecσconv n).
Proof.
  constructor.
  - intro v. induction v.
    + apply Vector.Forall2_nil.
    + apply Vector.Forall2_cons.
      * reflexivity.
      * apply IHv.
  - intros v1 v2 v3 H1 H2.
  unfold Tmcfvecσconv in *.
  induction H1.
    + dependent destruction H2.
      constructor.
    + dependent destruction H2.
    constructor.
      *  etransitivity; eassumption.
      * apply IHForall2.
        assumption.
Qed.

Global Instance TmASσeq_equivalence {n} : Equivalence (@Tmcfvecσeq n).
Proof.
  constructor.
  - intro v. induction v.
    + apply Vector.Forall2_nil.
    + apply Vector.Forall2_cons.
      * reflexivity.
      * apply IHv.
  - intros v ? ?. induction H.
    + apply Vector.Forall2_nil.
    + apply Vector.Forall2_cons.
      * now rewrite H.
      * exact IHForall2.
  - intros v1 v2 v3 H1 H2.
  unfold Tmcfvecσconv in *.
  induction H1.
    + dependent destruction H2.
      constructor.
    + dependent destruction H2.
    constructor.
      *  etransitivity; eassumption.
      * apply IHForall2.
        assumption.
Qed.

Global Instance Tmscf_longsnoc_eq_σstep_σconv {n} : Proper ( eq ==> Tmcfvecσstep ==> Tmscfσconv) (@AKcf_longsnoc n).
Proof.
  intros ? ? [] v' v vred.
  induction vred.
  - reflexivity.
  - cbn. now rewrite H, IHvred.
Qed.
Global Instance Tmscf_longsnoc_eq_σconv_σconv {n} : Proper ( eq ==> Tmcfvecσconv ==> Tmscfσconv) (@AKcf_longsnoc n).
Proof.
  intros ? ? [] v' v vred.
  induction vred.
  - reflexivity.
  - cbn. now rewrite H, IHvred.
Qed.
Global Instance Tmscf_longsnoc_eq_σeq_σeq {n} : Proper ( eq ==> Tmcfvecσeq ==> Tmscfσeq) (@AKcf_longsnoc n).
Proof.
  intros ? ? [] v' v vred.
  induction vred.
  - reflexivity.
  - cbn. now rewrite H, IHvred.
Qed.

Global Instance Tmscf_longsnoc_σstep_eq_σconv {n} : Proper (Tmscfσstep ==> eq ==> Tmscfσconv) (@AKcf_longsnoc n).
Proof.
  intros δ γ H v ? []; apply rt_step.
  induction v.
  { exact H. }
  cbn.
  apply (snoc_Tmscf_prpg _ _ (IHv v)).
Qed.
Global Instance AKcf_longsnoc_σconv {n} : Proper (Tmscfσconv ==> eq ==> Tmscfσconv) (@AKcf_longsnoc n).
Proof.
  intros δ γ H v ? [].
  induction v.
  { exact H. }
  cbn.
  now rewrite (IHv v).
Qed.

End Compatibility.

Lemma AKcf_jth_longsnoc_le {n} {δ: Tmscf} {v} {j} (le : j < n)
: cf_iter_π₂ j (AKcf_longsnoc δ v) -->* Vector.nth_order v le.
Proof.
  revert j le; induction v; intros j le.
  { exfalso; lia. }
  - simpl.
    destruct j.
    { unfold cf_iter_π₂, cf_iter_π₁; simpl.
      now rewrite cf_π₂beta. }
    rewrite cf_iter_π₂_snoc.
    assert (le' : j<n) by lia.
    rewrite (IHv _ le').
    now rewrite <-(Vector.nth_order_tl _ _ _ (h::v) le' le).
Qed.

Lemma AKcf_cf_iter_π₁_longsnoc_eq {n} {δ: Tmscf} {v: Vector.t Tmcf n}
: cf_iter_π₁ n (AKcf_longsnoc δ v) --s>* δ.
Proof.
  revert δ; induction v; intro δ.
  - reflexivity.
  - rewrite cf_iter_π₁_flip.
    cbn.
    rewrite cf_π₁beta.
    now rewrite IHv.
Qed.

Lemma AKcf_jth_longsnoc_ge {n} {δ: Tmscf} {v: Vector.t Tmcf n} {j} (le : j >= n)
: cf_iter_π₂ j (AKcf_longsnoc δ v) -->* cf_iter_π₂ (j-n) δ.
Proof.
  set (i := j-n).
  assert (H: j = i+n) by lia.
  rewrite H.
  clear le H.
  unfold cf_iter_π₂.
  rewrite <-Tmscf_nestediterπ₁.
  now rewrite AKcf_cf_iter_π₁_longsnoc_eq.
Qed.

Lemma AKcf_lift_snoc {δ a} : lift ⟨δ, a⟩ --s>* ⟨⟨δ ○ π1 id , a[π1 id]⟩,π2 id⟩.
Proof.
  unfold lift. now rewrite cf_snocomp.
Qed.

Lemma AKcf_longsnocomp {n δ} {v : Vector.t Tmcf n} {γ} :
(AKcf_longsnoc δ v) ○ γ --s>* AKcf_longsnoc δ ○ γ (Vector.map (Tmcf_subst^~ γ) v).
Proof.
  induction v.
  { reflexivity. }
  cbn.
  rewrite cf_snocomp.
  apply Tmscf_snoc_σconv; [|reflexivity].
  apply IHv.
Qed.

Lemma AKcf_lift_longsnoc {n} {δ: Tmscf} {v : Vector.t Tmcf n} :
  lift (AKcf_longsnoc δ v) --s>* (AKcf_longsnoc (δ ○ (π1 id)) ((π2 id) :: (Vector.map (Tmcf_subst ^~ (π1 id)) v))).
Proof.
  unfold lift.
  simpl.
  apply Tmscf_snoc_σconv; [|reflexivity].
  apply AKcf_longsnocomp.
Qed.
