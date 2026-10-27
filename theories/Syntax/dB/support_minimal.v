From CwFdeBruijn.Syntax.dB Require Import dB dBtm occur.

Fixpoint min_supp (a : dB) : nat :=
  match a with
  | dB_ref i => i+1
  | dB_app a b => max (min_supp a) (min_supp b)
  | dB_lam a => (min_supp a)-1
  end.

Fixpoint db_occur_minsupp (a:dB) (i:nat) {struct a}
 : OccurP i a -> i < min_supp a.
Proof.
  intro H.
  inversion H; cbn.
  - lia.
  - destruct a; try discriminate; inversion H1; subst.
    generalize (db_occur_minsupp _ _ Hx); lia.
  - destruct a; try discriminate; inversion H1; subst.
    generalize (db_occur_minsupp _ _ Hy); lia.
  - destruct a; try discriminate; inversion H1; subst.
    generalize (db_occur_minsupp _ _ Hy); lia.
Qed.

Lemma db_ContextP_minsupp_leq (a:dB) (i:nat)
 : ContextP i a -> min_supp a <= i.
Proof.
  revert i; induction a; intros j H.
  - cbn. unshelve eset (H i _); [|lia].
    apply (elimT (occurb_spec _ _)); cbn.
    apply Nat.eqb_refl.
  - generalize (IHa1 _ (ContextP_rator H)).
    generalize (IHa2 _ (ContextP_rand H)).
    cbn; lia.
  - cbn.
    generalize (IHa _ (ContextP_body H)).
    lia.
Qed.

Lemma db_ContextP_minsupp_is (a:dB) : ContextP (min_supp a) a.
Proof.
  intros i H.
  generalize (introT (occurb_spec _ _) H); clear H.
  revert i.
  induction a; intros j.
  - cbn; intros H. generalize (proj1 (Nat.eqb_eq _ _) H); lia.
  - cbn; intro H.
    destruct (proj1 (orb_true_iff _ _) H) as [H0|H0].
    + specialize (IHa1 _ H0); lia.
    + specialize (IHa2 _ H0); lia.
  - cbn; intros H.
    generalize (IHa _ H); lia.
Qed.