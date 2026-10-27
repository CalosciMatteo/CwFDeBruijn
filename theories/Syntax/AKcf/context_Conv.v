From CwFdeBruijn.Syntax.AKcf Require Export AKcf_Conv context.

(* Conversion preserve contexts *)
(* NOTE: it does not reflect them *)

Theorem cfcontext_preserved'' {p:nat} {x y : Tmcf}
  (red : Tmcfσstep' x y) (ctx : cfcontext p x)
  : cfcontext p y.
Proof.
  destruct red.
  - inversion ctx; subst.
    inversion Hx; subst.
    repeat econstructor; eassumption.
  - inversion ctx; subst.
    inversion Hδ; subst.
    assumption.
  - inversion ctx; subst.
    inversion Hx; subst.
    repeat econstructor; eassumption.
  - inversion ctx; subst.
    inversion Hx; subst.
    repeat econstructor; eassumption.
  - inversion ctx; subst.
    inversion Hx; subst.
    repeat econstructor; eassumption.
Qed.

Theorem cfassign_preserved'' {p q:nat} {δ σ : Tmscf}
  (red : Tmscfσstep' δ σ) (ass : cfassign p q δ)
  : cfassign p q σ.
Proof.
  destruct red.
  - inversion ass; subst.
    inversion Hδ₁; subst.
    repeat econstructor; eassumption.
  - inversion ass; subst.
    inversion Hδ₂; subst.
    assumption.
  - inversion ass; subst.
    inversion Hδ₁; subst.
    repeat econstructor; eassumption.
  - inversion ass; subst.
    inversion Hδ₁; subst.
    repeat econstructor; eassumption.
  - inversion ass; subst.
    inversion Hδ; subst.
    repeat econstructor; eassumption.
  - inversion ass; subst.
    inversion Hδ₁; subst.
    repeat econstructor; eassumption.
  - inversion ass; subst.
    inversion Hδ; subst.
    assumption.
Qed.

Fixpoint cfcontext_preserved' {p:nat} {x y : Tmcf}
  (red : Tmcfσstep x y) (ctx : cfcontext p x)
  : cfcontext p y
with cfassign_preserved' {p q : nat} {δ σ : Tmscf}
  (red : Tmscfσstep δ σ) (ass : cfassign p q δ)
  : cfassign p q σ.
Proof.
{ inversion red; subst.
  - exact (cfcontext_preserved'' H ctx).
  - inversion ctx; subst.
    econstructor.
    + apply (cfcontext_preserved' _ _ _ H).
      exact Hx.
    + exact Hδ.
  - inversion ctx; subst.
    econstructor.
    + exact Hx.
    + apply (cfassign_preserved' _ _ _ _ H).
      exact Hδ.
  - inversion ctx; subst.
    econstructor.
    apply (cfassign_preserved' _ _ _ _ H).
    exact Hδ.
  - inversion ctx; subst.
    constructor.
    + apply (cfcontext_preserved' _ _ _ H).
      exact Hx.
    + exact Hy.
  - inversion ctx; subst.
    constructor.
    + exact Hx.
    + apply (cfcontext_preserved' _ _ _ H).
      exact Hy.
  - inversion ctx; subst.
    constructor.
    apply (cfcontext_preserved' _ _ _ H).
    exact H2. }
{ inversion red; subst.
  - apply (cfassign_preserved'' H ass).
  - inversion ass; subst.
    constructor.
    + apply (cfassign_preserved' _ _ _ _ H).
      exact Hδ.
    + exact Hx.
  - inversion ass; subst.
    constructor.
    + exact Hδ.
    + apply (cfcontext_preserved' _ _ _ H).
      exact Hx.
  - inversion ass; subst.
    econstructor.
    + apply (cfassign_preserved' _ _ _ _ H).
      exact Hδ₁.
    + exact Hδ₂.
  - inversion ass; subst.
    econstructor.
    + exact Hδ₁.
    + apply (cfassign_preserved' _ _ _ _ H).
      exact Hδ₂.
  - inversion ass; subst.
    constructor.
    apply (cfassign_preserved' _ _ _ _ H).
    exact Hδ.
}
Qed.

Lemma cfcontext_preserved {p:nat} {x y : Tmcf}
  (red : x -->* y) (ctx : cfcontext p x)
  : cfcontext p y.
Proof.
  induction red.
  - apply (cfcontext_preserved' H ctx).
  - exact ctx.
  - apply IHred2.
    apply IHred1.
    exact ctx.
Qed.

Lemma cfassign_preserved {p q : nat} {δ σ : Tmscf}
  (red : δ --s>* σ) (ass : cfassign p q δ)
  : cfassign p q σ.
Proof.
  induction red.
  - apply (cfassign_preserved' H ass).
  - exact ass.
  - apply IHred2.
    apply IHred1.
    exact ass.
Qed.