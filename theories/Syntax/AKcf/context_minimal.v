From CwFdeBruijn.Syntax.AKcf Require Export context context_Conv.

(* Given a [Tmcf]/[Tmscf] a corresponding minimal [cfcontext]/[cfassign]
for it can be derived. This can be used to derive a
(propositional) type eliminating recursor for [cfcontext]/[cfassign] *)

Fixpoint cfcontext_weakening {x:Tmcf} {p r:nat}
  (ctx_x : cfcontext p x) (le_pq : p<=r) {struct ctx_x}
  : cfcontext r x
with cfassign_weakening {δ:Tmscf} {p q: nat}
  (ass_pqδ : cfassign p q δ) (i:nat) {struct ass_pqδ}
  : cfassign (p+i) (q+i) δ.
Proof.
{ destruct ctx_x.
  - assert (E: r = p + (r - p)). {lia. } rewrite E.
    eapply cfcontext_subst.
    + apply (cfcontext_weakening _ _ (q+(r - p)) ctx_x).
      lia.
    + apply (cfassign_weakening _ _ _ Hδ).
  - eapply (cfcontext_π₂ (q:= q + (r-p))).
    assert (E: r = p + (r - p)). {lia. } rewrite E.
    assert (E2 : S (q + (p + (r - p) - p)) = (S q) + (r - p)). {lia. } rewrite <-E at 2.
    apply (cfassign_weakening _ _ _ Hδ (r-p)).
  - eapply cfcontext_app.
    + apply (cfcontext_weakening _ _ _ ctx_x1 le_pq).
    + apply (cfcontext_weakening _ _ _ ctx_x2 le_pq).
  - eapply cfcontext_lam.
    refine (cfcontext_weakening _ _ (S r) ctx_x _).
    apply le_n_S.
    exact le_pq.
}
{ destruct ass_pqδ.
  - eapply cfassign_snoc.
    + fold (q+i).
      apply (cfassign_weakening _ _ _ ass_pqδ).
    + apply (cfcontext_weakening _ _ _ Hx).
      lia.
  - apply cfassign_id.
  - apply (cfassign_comp (q:= q+i)).
    + apply (cfassign_weakening _ _ _ ass_pqδ1).
    + apply (cfassign_weakening _ _ _ ass_pqδ2).
  - apply cfassign_π₁.
    assert (E: S (q + i) = (S q) + i). {lia. } rewrite E.
    apply (cfassign_weakening _ _ _ ass_pqδ).
}
Defined.

Lemma cfassign_weakening' {δ:Tmscf} {p q: nat}
(ass_pqδ : cfassign p q δ) (i:nat)
: cfassign (i+p) (i+q) δ.
Proof.
  rewrite (Nat.add_comm _ p).
  rewrite (Nat.add_comm _ q).
  apply cfassign_weakening.
  exact ass_pqδ.
Qed.

Section MinimalContext.

  Record MinimalContext (x:Tmcf) : Type := make_MinimalContext {
    minctx : nat;
    minctx_ctx : cfcontext minctx x;
    minctx_minimal : forall i, cfcontext i x -> minctx <= i
  }.

  Record MinimalAssign (δ:Tmscf) : Type := make_MinimalAssign {
    minass_p : nat;
    minass_q : nat;
    minass_ass : cfassign minass_p minass_q δ;
    minass_minimal : forall p q, cfassign p q δ
      -> exists i, (p = minass_p + i) /\  (q = minass_q + i)
  }.

  Fixpoint getMinimalContext (x:Tmcf) {struct x}
    : MinimalContext x
  with getMinimalAssign (δ:Tmscf) {struct δ}
    : MinimalAssign δ.
  Proof.
  { destruct x.
    - destruct (getMinimalContext x) as [q ctx_qx q_minimal].
      destruct (getMinimalAssign δ) as [p r ass_δpr pr_minimal].
      eapply make_MinimalContext.
      + refine (cfcontext_subst (q:= max q r) _ _).
        * apply (cfcontext_weakening ctx_qx).
          lia.
        * assert (E: max q r = r + ((max q r) - r)). {lia. } rewrite E.
          apply (cfassign_weakening ass_δpr).
      + intros p' ctx.
        inversion ctx; subst.
        specialize (q_minimal q0 Hx).
        destruct (pr_minimal _ _ Hδ) as [i [? ?]].
        lia.
    - destruct (getMinimalAssign δ) as [p r ass_δpr pr_minimal].
      eapply make_MinimalContext.
      + refine (cfcontext_π₂ (q:= pred r) _).
        assert (E : (S (pred r)) = r+((S (pred r))-r)). {lia. }
        rewrite E.
        apply (cfassign_weakening ass_δpr).
      + intros i ctx.
        inversion ctx; subst.
        specialize (pr_minimal _ _ Hδ) as [j ?].
        lia.
    - destruct (getMinimalContext x1) as [p1 ctx_p1x1 p1_minimal].
      destruct (getMinimalContext x2) as [p2 ctx_p2x2 p2_minimal].
      eapply make_MinimalContext.
      + apply (cfcontext_app (p:= max p1 p2)).
        * apply (cfcontext_weakening ctx_p1x1).
          lia.
        * apply (cfcontext_weakening ctx_p2x2).
          lia.
      + intros m' ctx.
        inversion ctx; subst.
        specialize (p1_minimal _ Hx).
        specialize (p2_minimal _ Hy).
        lia.
    - destruct (getMinimalContext x) as [p ctx_px p_minimal].
      (* Note : it may be p = 0 = pred p. Everything still works *)
      eapply make_MinimalContext.
      + apply (cfcontext_lam (p:= pred p)).
        apply (cfcontext_weakening ctx_px).
        lia.
      + intros p' ctx.
        inversion ctx; subst.
        specialize (p_minimal _ H1).
        lia. }
  { destruct δ.
    - destruct (getMinimalContext x) as [q ctx_qx q_minimal].
      destruct (getMinimalAssign δ) as [p r ass_δpr pr_minimal].
      eapply make_MinimalAssign.
      + eapply (cfassign_snoc (p:= max p q)).
        * assert (E: max p q = p + (max p q - p)). {lia. } rewrite E.
          apply (cfassign_weakening ass_δpr (max p q - p)).
        * eapply (cfcontext_weakening ctx_qx).
          lia.
      + intros p' q' ass.
        inversion ass; subst.
        specialize (q_minimal _ Hx).
        specialize (pr_minimal _ _ Hδ) as [j [? ?]].
        exists (p + j - max p q).
        lia.
    - eapply make_MinimalAssign.
      + exact (cfassign_id 0).
      + intros p q ass.
        inversion ass; subst.
        exists q.
        lia.
    - destruct (getMinimalAssign δ1) as [q1 r ass_δq1r q1r_minimal].
      destruct (getMinimalAssign δ2) as [p q2 ass_δpq2 pq2_minimal].
      eapply make_MinimalAssign.
      + apply (cfassign_comp (q:= max q1 q2)).
        * assert (E: max q1 q2 = q1 + ((max q1 q2) - q1)). {lia. } rewrite E.
          eapply (cfassign_weakening ass_δq1r).
        * assert (E: max q1 q2 = q2 + ((max q1 q2) - q2)). {lia. } rewrite E.
        eapply (cfassign_weakening ass_δpq2).
      + intros p' q' ass.
        inversion ass; subst.
        specialize (q1r_minimal _ _ Hδ₁) as [j [? ?]].
        specialize (pq2_minimal _ _ Hδ₂) as [j' [? ?]].
        subst.
        exists (j' - ((max q1 q2) - q2)).
        lia.
    - destruct (getMinimalAssign δ) as [p q ass_δpq pq_minimal].
      eapply make_MinimalAssign.
      + eapply (cfassign_π₁ (q := pred q)).
        assert (E: S (pred q) = q + (S (pred q) - q)). {lia. } rewrite E.
        eapply (cfassign_weakening ass_δpq).
      + intros p' q' ass.
        inversion ass; subst.
        specialize (pq_minimal _ _ Hδ) as [j [? ?]].
        subst.
        exists( j - (S (pred q) - q)).
        lia. }
  Defined.

End MinimalContext.

Definition Minctx x := minctx _ (getMinimalContext x).
Definition Minctx_ctx x := minctx_ctx _ (getMinimalContext x).
Definition Minctx_minimal x := minctx_minimal _ (getMinimalContext x).
Definition Minass_p δ := minass_p _ (getMinimalAssign δ).
Definition Minass_q δ := minass_q _ (getMinimalAssign δ).
Definition Minass_ass δ := minass_ass _ (getMinimalAssign δ).
Definition Minass_minimal δ := minass_minimal _ (getMinimalAssign δ).

Lemma Minass_q_comp_beta' (δ σ : Tmscf)
  : Minass_q (Tmscf_comp δ σ) =
    Minass_q δ
      + (max (Minass_p δ) (Minass_q σ)
      - (Minass_p δ)).
Proof.
  unfold Minass_p, Minass_q.
  simpl.
  destruct (getMinimalAssign δ).
  destruct (getMinimalAssign σ).
  reflexivity.
Qed.

Lemma Minass_q_comp_beta (δ σ : Tmscf)
  : Minass_q (Tmscf_comp δ σ) =
    Minass_q δ
      + ((Minass_q σ)
      - (Minass_p δ)).
Proof.
  rewrite Minass_q_comp_beta'.
  lia.
Qed.

Lemma Minass_p_comp_beta' (δ σ : Tmscf)
  : Minass_p (Tmscf_comp δ σ) =
    Minass_p σ
    + (max (Minass_p δ) (Minass_q σ)
    - Minass_q σ).
Proof.
  unfold Minass_p, Minass_q.
  simpl.
  destruct (getMinimalAssign δ).
  destruct (getMinimalAssign σ).
  reflexivity.
Qed.

Lemma Minass_p_comp_beta (δ σ : Tmscf)
  : Minass_p (Tmscf_comp δ σ) =
    Minass_p σ
    + ((Minass_p δ)
    - Minass_q σ).
Proof.
  rewrite Minass_p_comp_beta'.
  lia.
Qed.

Lemma Minass_q_snoc_beta' (δ : Tmscf) (x:Tmcf)
  : Minass_q (Tmscf_snoc δ x) = S ((Minass_q δ) + ((max (Minass_p δ) (Minctx x)) - Minass_p δ)).
Proof.
  unfold Minass_p, Minass_q, Minctx. simpl.
  destruct (getMinimalContext x).
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Lemma Minass_q_snoc_beta (δ : Tmscf) (x:Tmcf)
  : Minass_q (Tmscf_snoc δ x) = S ((Minass_q δ) + ((Minctx x) - Minass_p δ)).
Proof.
  rewrite Minass_q_snoc_beta'.
  lia.
Qed.

Lemma Minass_p_snoc_beta (δ : Tmscf) (x:Tmcf)
  : Minass_p (Tmscf_snoc δ x) = max (Minass_p δ) (Minctx x).
Proof.
  unfold Minass_p, Minass_q, Minctx. simpl.
  destruct (getMinimalContext x).
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Lemma Minass_q_π₁_beta (δ : Tmscf)
  : Minass_q (Tmscf_π₁ δ) = pred (Minass_q δ).
Proof.
  unfold Minass_q. simpl.
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Lemma Minass_p_π₁_beta (δ : Tmscf)
  : Minass_p (Tmscf_π₁ δ) = (Minass_p δ) + (S (pred (Minass_q δ)) - (Minass_q δ)).
Proof.
  unfold Minass_p, Minass_q. simpl.
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Lemma Minctx_subst_beta' {x:Tmcf} {δ: Tmscf}
  : Minctx (Tmcf_subst x δ) = Minass_p δ + ((max (Minctx x) (Minass_q δ)) - (Minass_q δ)).
Proof.
  unfold Minass_p, Minass_q, Minctx. simpl.
  destruct (getMinimalContext x).
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Lemma Minctx_subst_beta {x:Tmcf} {δ: Tmscf}
  : Minctx (Tmcf_subst x δ) = Minass_p δ + ((Minctx x) - (Minass_q δ)).
Proof.
  rewrite Minctx_subst_beta'.
  lia.
Qed.

Lemma Minctx_π₂_beta' {δ: Tmscf}
  : Minctx (Tmcf_π₂ δ)
  = Minass_p δ + (S (pred (Minass_q δ) ) - (Minass_q δ) ).
Proof.
  unfold Minass_p, Minass_q, Minctx. simpl.
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

(* Minctx (Tmcf_π₂ δ) = Minass_p δ + χ0 (Minass_q δ)*)
Lemma Minctx_π₂_beta {δ: Tmscf}
  : Minctx (Tmcf_π₂ δ)
  = Minass_p δ + (S (pred (Minass_q δ) ) - (Minass_q δ) ).
Proof.
  unfold Minass_p, Minass_q, Minctx. simpl.
  destruct (getMinimalAssign δ).
  reflexivity.
Qed.

Ltac Minbeta :=
  try rewrite
    ?Minass_q_snoc_beta, ?Minass_p_snoc_beta,
    ?Minass_p_comp_beta, ?Minass_q_comp_beta,
    ?Minass_p_π₁_beta, ?Minass_q_π₁_beta,
    ?Minctx_subst_beta.

Lemma Minctx_conv {x x':Tmcf} (H: x --> x') : Minctx x >= Minctx x'.
Proof.
  apply Minctx_minimal.
  apply (cfcontext_preserved' H (Minctx_ctx x)).
Qed.

Lemma Minass_conv' {δ δ' : Tmscf} (H: Tmscfσstep' δ δ')
  : Minass_q δ = Minass_q δ' + (Minass_q δ - Minass_q δ') /\
    Minass_p δ = Minass_p δ' + (Minass_q δ - Minass_q δ').
Proof.
  destruct H.
  all: try (repeat Minbeta; lia).
  all: (Minbeta; cbn; lia).
Qed.

Lemma Minass_conv {δ δ' : Tmscf} (H: Tmscfσstep δ δ')
  : exists i,
      Minass_q δ = Minass_q δ' + i /\
      Minass_p δ = Minass_p δ' + i.
Proof.
  split with (Minass_q δ - Minass_q δ').
  induction H.
  { apply (Minass_conv' H). }
  all: try (Minbeta; lia).
  Minbeta.
  specialize (Minctx_conv H).
  lia.
Qed.

Lemma Minass_conv_corollary {p q q':nat} {δ δ' : Tmscf}
  (red: Tmscfσstep δ δ')
  (ass: cfassign p q δ)
  (ass': cfassign p q' δ')
  : Minass_q δ' + (p - Minass_p δ')
  = Minass_q δ  + (p - Minass_p δ).
Proof.
  destruct (Minass_conv red) as [? [? ?]].
  destruct (Minass_minimal _ _ _ ass) as [? [? ?]].
  destruct (Minass_minimal _ _ _ ass') as [? [? ?]].
  unfold Minass_q, Minass_p in *.
  lia.
Qed.

Lemma Minass_conv_corollary' {p p' q :nat} {δ δ' : Tmscf}
  (red: Tmscfσstep δ δ')
  (ass: cfassign p q δ)
  (ass': cfassign p' q δ')
  : Minass_p δ' + (q - Minass_q δ')
  = Minass_p δ  + (q - Minass_q δ).
Proof.
  destruct (Minass_conv red) as [? [? ?]].
  destruct (Minass_minimal _ _ _ ass) as [? [? ?]].
  destruct (Minass_minimal _ _ _ ass') as [? [? ?]].
  unfold Minass_q, Minass_p in *.
  lia.
Qed.

Lemma cfassign_sameDom {p p' q : nat} {δ : Tmscf}
  (ass: cfassign p q δ) (ass' : cfassign p' q δ)
  : p = p'.
  Proof.
    destruct (Minass_minimal _ _ _ (ass)) as [i [? ?]].
    destruct (Minass_minimal _ _ _ (ass')) as [j [? ?]].
    lia.
  Qed.

Definition cfcontext_spec {p:nat} (x:Tmcf)
  : reflect (cfcontext p x) ((Minctx x) <=? p).
Proof.
  apply (equivP (P:= (Minctx x <= p))).
  { apply Nat.leb_spec0. }
  split.
  - intro leq.
    refine (cfcontext_weakening _ leq).
    apply minctx_ctx.
  - intro ctx_px.
    apply (Minctx_minimal x p ctx_px).
Qed.

Section PureInversion_cfcontext.

  Lemma contextof_subst {p x δ} (ctx : cfcontext p (Tmcf_subst x δ))
    : cfcontext (Minass_q δ + (p - Minass_p δ)) x.
  Proof.
    inversion ctx; subst.
    destruct (Minass_minimal δ _ _ Hδ) as [i [? ?]].
    assert (E: q = (Minass_q δ + (p - Minass_p δ))).
    { unfold Minass_q, Minass_p. lia. }
    destruct E.
    exact Hx.
  Qed.

  Lemma assignof_subst {p x δ} (ctx : cfcontext p (Tmcf_subst x δ))
    : cfassign p (Minass_q δ + (p - Minass_p δ)) δ.
  Proof.
    inversion ctx; subst.
    destruct (Minass_minimal δ _ _ Hδ) as [i [? ?]].
    assert (E: q = (Minass_q δ + (p - Minass_p δ))).
    { unfold Minass_q, Minass_p. lia. }
    destruct E.
    exact Hδ.
  Qed.

  Lemma inversion_cfcontext_subst {p x δ} (ctx : cfcontext p (Tmcf_subst x δ))
    : ctx = cfcontext_subst (contextof_subst ctx) (assignof_subst ctx).
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma assignof_π₂ {p δ} (ctx : cfcontext p (Tmcf_π₂ δ))
    : cfassign p (S (pred (Minass_q δ + (p - Minass_p δ)))) δ.
  Proof.
    inversion ctx; subst.
    destruct (Minass_minimal δ _ _ Hδ) as [i [? ?]].
    assert (E : S q = S (pred (Minass_q δ + (p - Minass_p δ)))).
    { unfold Minass_p, Minass_q. lia. }
    destruct E.
    exact Hδ.
  Qed.

  Lemma inversion_cfcontext_π₂ {p δ} (ctx : cfcontext p (Tmcf_π₂ δ))
    : ctx = cfcontext_π₂ (assignof_π₂ ctx).
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma contextof_rator {p x y} (ctx : cfcontext p (Tmcf_app x y))
    : cfcontext p x.
  Proof.
    inversion ctx.
    exact Hx.
  Qed.

  Lemma contextof_rand {p x y} (ctx : cfcontext p (Tmcf_app x y))
    : cfcontext p y.
  Proof.
    inversion ctx.
    exact Hy.
  Qed.

  Lemma inversion_cfcontext_app {p x y} (ctx : cfcontext p (Tmcf_app x y))
    : ctx = cfcontext_app (contextof_rator ctx) (contextof_rand ctx).
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma contextof_lam {p x} (ctx : cfcontext p (Tmcf_lam x))
    : cfcontext (S p) x.
  Proof.
    inversion ctx.
    exact H1.
  Defined.

  Lemma inversion_cfcontext_lam {p x} (ctx : cfcontext p (Tmcf_lam x))
    : ctx = cfcontext_lam (contextof_lam ctx).
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma contextof_snoc_false {p δ x} (ass : cfassign p 0 (Tmscf_snoc δ x)) : False.
  Proof.
    inversion ass.
  Qed.

  Lemma contextof_snoc {p q δ x} (ass : cfassign p (S q) (Tmscf_snoc δ x))
    : (cfcontext p x).
  Proof.
    inversion ass.
    exact Hx.
  Qed.

  Lemma assignof_snoc {p q δ x} (ass : cfassign p (S q) (Tmscf_snoc δ x))
    : (cfassign p q δ).
  Proof.
    inversion ass.
    exact Hδ.
  Qed.

  Lemma inversion_cfassign_snoc {p q δ x}
    (ass : cfassign p (S q) (Tmscf_snoc δ x))
    : ass = cfassign_snoc (assignof_snoc ass) (contextof_snoc ass).
  Proof.
    apply proof_irrelevance.
  Qed.

  Definition assignlof_comp {p r δ₁ δ₂}
    (ass : cfassign p r (Tmscf_comp δ₁ δ₂))
    : cfassign (Minass_p δ₁ + (r - Minass_q δ₁)) r δ₁.
  Proof.
    inversion ass; subst.
    destruct (Minass_minimal δ₁ _ _ Hδ₁) as [i [? ?]].
    destruct (Minass_minimal δ₂ _ _ Hδ₂) as [j [? ?]].
    assert (E : q = (Minass_p δ₁ + (r - Minass_q δ₁))).
    { unfold Minass_p, Minass_q. lia. }
    destruct E.
    exact Hδ₁.
  Qed.

  Definition assignrof_comp {p r δ₁ δ₂}
    (ass : cfassign p r (Tmscf_comp δ₁ δ₂))
    : cfassign p (Minass_p δ₁ + (r - Minass_q δ₁)) δ₂.
  Proof.
    inversion ass; subst.
    destruct (Minass_minimal δ₁ _ _ Hδ₁) as [i [? ?]].
    destruct (Minass_minimal δ₂ _ _ Hδ₂) as [j [? ?]].
    assert (E : q = (Minass_p δ₁ + (r - Minass_q δ₁))).
    { unfold Minass_p, Minass_q. lia. }
    destruct E.
    exact Hδ₂.
  Qed.

  Lemma inversion_cfassign_comp {p r δ₁ δ₂}
    (ass : cfassign p r (Tmscf_comp δ₁ δ₂))
    : ass = cfassign_comp (assignlof_comp ass) (assignrof_comp ass).
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma assignof_π₁ {p q δ} (ass : cfassign p q (Tmscf_π₁ δ))
  : cfassign p (S q) δ.
  Proof.
    inversion ass.
    exact Hδ.
  Qed.

  Lemma inversion_cfassign_π₁ {p q δ} (ass : cfassign p q (Tmscf_π₁ δ))
  : ass = cfassign_π₁ (assignof_π₁ ass).
  Proof.
    apply proof_irrelevance.
  Qed.
End PureInversion_cfcontext.

Theorem cfcontext_recT
  (P : nat -> Tmcf -> Type)
  (IH1 : forall (q : nat) (x : Tmcf), cfcontext q x -> P q x -> forall (p : nat) (δ : Tmscf), cfassign p q δ -> P p (Tmcf_subst x δ))
  (IH2 : forall (p q : nat) (δ : Tmscf), cfassign p (S q) δ -> P p (Tmcf_π₂ δ))
  (IH3 : forall (p : nat) (x y : Tmcf), cfcontext p x -> P p x -> cfcontext p y -> P p y -> P p (Tmcf_app x y))
  (IH4 : forall (p : nat) (x : Tmcf), cfcontext (S p) x -> P (S p) x -> P p (Tmcf_lam x))
  (p : nat) (x : Tmcf) (ctx_px : cfcontext p x)
  : P p x.
Proof.
  revert p ctx_px.
  induction x; intros p ctx_px.
  - apply (IH1 ((Minass_q δ) + ((p - Minass_p δ)))).
    + apply (contextof_subst ctx_px).
    + apply (IHx _ (contextof_subst ctx_px)).
    + apply (assignof_subst ctx_px).
  - apply (IH2 _ (pred (Minass_q δ + (p - Minass_p δ))) _ (assignof_π₂ ctx_px)).
  - refine (IH3 _ _ _ (contextof_rator ctx_px) _ (contextof_rand ctx_px) _).
    + apply (IHx1 _ (contextof_rator ctx_px)).
    + apply (IHx2 _ (contextof_rand ctx_px)).
  - refine (IH4 _ _ (contextof_lam ctx_px) _).
    apply IHx; exact (contextof_lam ctx_px).
Defined.

Definition cfcontext_rec := cfcontext_recT.

Theorem cfassign_recT
  (P : nat -> nat -> Tmscf -> Type)
  (H1 : forall (p q : nat) (δ : Tmscf), cfassign p q δ -> P p q δ -> forall x : Tmcf, cfcontext p x -> P p (S q) (Tmscf_snoc δ x))
  (H2 : forall (p:nat), P p p Tmscf_id)
  (H3 : forall (q r : nat) (δ₁ : Tmscf), cfassign q r δ₁ -> P q r δ₁ -> forall (p : nat) (δ₂ : Tmscf), cfassign p q δ₂ -> P p q δ₂ -> P p r (Tmscf_comp δ₁ δ₂))
  (H4 : forall (p q : nat) (δ : Tmscf),
  cfassign p (S q) δ -> P p (S q) δ -> P p q (Tmscf_π₁ δ))
  (p q : nat) (δ : Tmscf) (ass : cfassign p q δ)
  : P p q δ.
Proof.
  revert p q ass.
  induction δ; intros p q ass.
  - destruct q.
    { exfalso. apply (contextof_snoc_false ass). }
    apply H1.
    + apply (assignof_snoc ass).
    + apply (IHδ _ _ (assignof_snoc ass)).
    + apply (contextof_snoc ass).
  - destruct (contextof_id ass).
    apply H2.
  - apply (H3 (Minass_p δ1 + (q - Minass_q δ1))).
    + apply (assignlof_comp ass).
    + apply (IHδ1 _ _ (assignlof_comp ass)).
    + exact (assignrof_comp ass).
    + apply (IHδ2 _ _ (assignrof_comp ass)).
  - apply (H4 _ _ _ (assignof_π₁ ass)).
    apply (IHδ _ _ (assignof_π₁ ass)).
Defined.

Definition cfassign_rec := cfassign_recT.