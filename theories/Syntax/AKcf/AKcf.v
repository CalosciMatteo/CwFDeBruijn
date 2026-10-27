From CwFdeBruijn.Syntax Require Export Setup.
From Stdlib Require Import Bool.


(* Unscoped Model for the Untyped lambda calculus binding signature *)
Inductive Tmscf : Type :=
  | Tmscf_snoc (δ : Tmscf) (x : Tmcf) : Tmscf
  | Tmscf_id : Tmscf
  | Tmscf_comp (δ₁ : Tmscf) (δ₂ : Tmscf) : Tmscf
  | Tmscf_π₁ (δ : Tmscf) : Tmscf
with Tmcf : Type :=
  | Tmcf_subst (x : Tmcf) (δ : Tmscf) : Tmcf
  | Tmcf_π₂ (δ : Tmscf) : Tmcf
  | Tmcf_app (x : Tmcf) (y : Tmcf) : Tmcf
  | Tmcf_lam (x : Tmcf) : Tmcf.

Definition lift (δ:Tmscf) : Tmscf :=
  Tmscf_snoc (Tmscf_comp δ (Tmscf_π₁ Tmscf_id)) (Tmcf_π₂ Tmscf_id).

Definition iter_lift := iter lift.

Definition cf_iter_π₁ := iter Tmscf_π₁.

Definition cf_iter_π₁_flip i δ
  : cf_iter_π₁ (S i) δ = (cf_iter_π₁ i (Tmscf_π₁  δ)) := iter_flip Tmscf_π₁ i δ.

Definition cf_iter_π₂ i (δ : Tmscf) :=
  Tmcf_π₂ (cf_iter_π₁ i δ).

Definition Tmcf_ref i :Tmcf :=
  cf_iter_π₂ i (Tmscf_id).

Section cf_iter_π₁.

  Inductive cf_iter_π₁idP : Tmscf -> Prop :=
  | cf_iter_π₁idP_id
    : cf_iter_π₁idP Tmscf_id
  | cf_iter_π₁idP_π₁ {δ : Tmscf} (Hδ : cf_iter_π₁idP δ)
    : cf_iter_π₁idP (Tmscf_π₁ δ).

  Fixpoint cf_iter_π₁idb (δ: Tmscf) : bool :=
  match δ with
    | Tmscf_snoc δ x => false
    | Tmscf_id => true
    | Tmscf_comp δ₁ δ₂ => false
    | Tmscf_π₁ δ => cf_iter_π₁idb δ
  end.

  Lemma cf_iter_π₁id_spec (δ: Tmscf) : reflect (cf_iter_π₁idP δ) (cf_iter_π₁idb δ).
  Proof.
    induction δ; simpl.
    + intros.
      apply ReflectF.
      intros abs.
      solve_by_invert.
    + apply ReflectT.
      apply cf_iter_π₁idP_id.
    + apply ReflectF.
      intro; solve_by_invert.
    + apply ((equivP (P:=cf_iter_π₁idP δ)) _ _ IHδ).
      split.
      - apply cf_iter_π₁idP_π₁.
      - intro H. inversion H; assumption.
  Qed.

  Definition cf_iter_π₁idP_rec
    (P : Tmscf -> Type)
    (X1 : P Tmscf_id)
    (X2 : forall δ : Tmscf, cf_iter_π₁idP δ -> P δ -> P (Tmscf_π₁ δ))  (δ : Tmscf) (H : cf_iter_π₁idP δ)
    : P δ.
  Proof.
    assert (E := (proj1 (reflect_iff _ _ (cf_iter_π₁id_spec δ)) H)).
    induction δ; try discriminate E.
    - apply X1.
    - apply X2.
      + inversion H.
        exact Hδ.
      + apply IHδ.
        * inversion H. exact Hδ.
        * exact E.
  Defined.

  Lemma cf_iter_π₁idP_dec (δ: Tmscf) : {cf_iter_π₁idP δ} + {not (cf_iter_π₁idP δ)}.
  Proof.
    apply (reflect_dec (cf_iter_π₁idP δ) (cf_iter_π₁idb δ)).
    apply cf_iter_π₁id_spec.
  Qed.

  Lemma Tmscfσvalue_cf_iter_π₁id (i : nat) : cf_iter_π₁idP (cf_iter_π₁ i Tmscf_id).
  Proof.
    induction i as [i IHi] using lt_wf_ind.
    induction i as [| [ | i] _ ].
    - exact cf_iter_π₁idP_id.
    - apply cf_iter_π₁idP_π₁.
      apply cf_iter_π₁idP_id.
    - simpl.
      apply cf_iter_π₁idP_π₁.
      apply (IHi (S i)).
      lia.
  Qed.

  Lemma cf_iter_π₁idP_to_cf_iter_π₁id {δ: Tmscf} (Hδ: cf_iter_π₁idP δ) : { i & δ = cf_iter_π₁ i Tmscf_id}.
  Proof.
    induction δ.
    - exfalso. inversion Hδ.
    - split with 0. reflexivity.
    - exfalso. inversion Hδ.
    - destruct IHδ as [i ?].
      + inversion Hδ; assumption.
      + split with (S i).
        unfold cf_iter_π₁.
        simpl.
        f_equal.
        exact e.
  Qed.

  Lemma cf_iter_π₁id_inj {i j}
    : cf_iter_π₁ i Tmscf_id = cf_iter_π₁ j Tmscf_id -> i=j.
  Proof.
    revert j; induction i; intro j.
    { destruct j.
      - reflexivity.
      - cbn. intro H. discriminate H. }
    destruct j.
    - cbn; intro H; discriminate H.
    - cbn; intro H.
    assert (i=j); [|lia].
    apply IHi.
    inversion H.
    reflexivity.  
  Qed.

End cf_iter_π₁.

(* Equality decidability for AKcf *)

Lemma deceq_Tmscf : forall (δ σ : Tmscf), {δ = σ} + {δ <> σ}
with deceq_Tmcf : forall (x y : Tmcf), {x = y} + {x <> y}.
Proof.
  all:
    decide equality.
Defined.

Definition Tmscf_beq (δ σ : Tmscf) : bool :=
  if deceq_Tmscf δ σ then true else false.
Definition Tmcf_beq (x y : Tmcf) : bool :=
  if deceq_Tmcf x y then true else false.

Lemma Tmscf_eq_spec (δ σ : Tmscf) : reflect (δ = σ) (Tmscf_beq δ σ).
Proof.
  unfold Tmscf_beq.
  destruct (deceq_Tmscf δ σ).
  - apply ReflectT; assumption.
  - apply ReflectF; assumption.
Qed.

Lemma Tmcf_eq_spec (x y : Tmcf) : reflect (x = y) (Tmcf_beq x y).
Proof.
  unfold Tmcf_beq.
  destruct (deceq_Tmcf x y).
  - apply ReflectT; assumption.
  - apply ReflectF; assumption.
Qed.
