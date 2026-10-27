From CwFdeBruijn.Syntax.AKcf Require Export AKcf.

Inductive cfassign : forall (p q : nat) (δ : Tmscf), Prop :=
  | cfassign_snoc {p q} {δ} (Hδ: cfassign p q δ) {x} (Hx : cfcontext p x)
    : cfassign p (S q) (Tmscf_snoc δ x)
  | cfassign_id p : cfassign p p Tmscf_id
  | cfassign_comp {q r} {δ₁} (Hδ₁ : cfassign q r δ₁) {p} {δ₂} (Hδ₂ : cfassign p q δ₂)
    : cfassign p r (Tmscf_comp δ₁ δ₂)
  | cfassign_π₁ {p q} {δ} (Hδ : cfassign p (S q) δ) : cfassign p q (Tmscf_π₁ δ)

with cfcontext : forall (p:nat) (x:Tmcf), Prop :=
  | cfcontext_subst {q} {x} (Hx : cfcontext q x) {p δ} (Hδ : cfassign p q δ): cfcontext p (Tmcf_subst x δ)
  | cfcontext_π₂ {p q} {δ} (Hδ : cfassign p (S q) δ): cfcontext p (Tmcf_π₂ δ)
  | cfcontext_app {p} {x y} (Hx : cfcontext p x) (Hy : cfcontext p y)
    : cfcontext p (Tmcf_app x y)
  | cfcontext_lam {p} {x} (H : cfcontext (S p) x)
    : cfcontext p (Tmcf_lam x).

Definition contextof_id {p q} : cfassign p q Tmscf_id -> p = q.
Proof.
  intro H.
  inversion H.
  reflexivity.
Defined.

Lemma cfassign_iter_π₁ δ i {p q} : cfassign p (i + q) δ -> cfassign p q (cf_iter_π₁ i δ).
Proof.
  revert δ.
  induction i; intros δ H.
  + exact H.
  + rewrite cf_iter_π₁_flip.
    apply IHi.
    refine (cfassign_π₁ _).
    exact H.
Defined.

Lemma cfcontext_ref {p i} (H : i < p) : cfcontext p (Tmcf_ref i).
Proof.
  revert i H.
  induction p; intros i H.
  {
    exfalso.
    inversion H.
  }
  induction i.
  {
    simpl.
    refine (cfcontext_π₂ _).
    apply cfassign_id.
  }

  unfold Tmcf_ref, cf_iter_π₂.
  rewrite cf_iter_π₁_flip.
  refine (cfcontext_π₂ _).
  refine (cfassign_iter_π₁ _ _ _).
  refine (cfassign_π₁ _).
  Unshelve.
  2: { exact (Nat.pred (p - i)). }
  assert (H' : i + S (Nat.pred ((p - i))) = p). { lia. }
  apply (eq_rect (S p) (fun x => cfassign (S p) x Tmscf_id)).
  { apply cfassign_id. }
  f_equal.
  rewrite H' at 1.
  reflexivity.
Qed.