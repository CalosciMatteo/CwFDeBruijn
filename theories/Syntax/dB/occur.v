From CwFdeBruijn.Syntax.dB Require  Export dB.

(* Express that i-th ref appears in x *)
Inductive OccurP : forall (i : nat) (x : dB), Prop :=
  | OccurP_ref i : OccurP i (dB_ref i)
  | OccurP_rator i x y (Hx : OccurP i x) : OccurP i (dB_app x y)
  | OccurP_rand i x y (Hy : OccurP i y) : OccurP i (dB_app x y)
  | OccurP_body i x (Hy : OccurP (S i) x) : OccurP i (dB_lam x).

Derive Inversion_clear OccurP_ref_inversion
  with (forall i j, OccurP i (dB_ref j)).

Derive Inversion_clear OccurP_app_inversion
  with (forall i x y, OccurP i (dB_app x y)).

Derive Inversion_clear OccurP_lam_inversion
  with (forall i x, OccurP i (dB_lam x)).

Lemma OccurP_index {i j} (H : OccurP i (dB_ref j)) : i = j.
Proof.
inversion H using OccurP_ref_inversion.
reflexivity.
Qed.

Lemma OccurP_app {i x y} (H : OccurP i (dB_app x y)) :
  OccurP i x \/ OccurP i y.
Proof.
inversion H using OccurP_app_inversion; auto.
Qed.

Lemma OccurP_lam {i x} (H : OccurP i (dB_lam x)) : OccurP (S i) x.
Proof.
inversion H using OccurP_lam_inversion. auto.
Qed.

Lemma OccurP_reindex {x i} (Hi : OccurP i x) :
  forall {f}, OccurP (f i) (reindex f x).
Proof.
induction Hi.
- intros. simpl. apply OccurP_ref.
- intros. simpl. apply OccurP_rator. auto.
- intros. simpl. apply OccurP_rand. auto.
- intros. simpl. apply OccurP_body.
  assert (H := IHHi (slide f)).
  exact H.
Qed.

Lemma OccurP_dec x : forall i, {OccurP i x} + {~ OccurP i x}.
Proof.
induction x as [j | x Hx y Hy | x Hx]; intros i.
- destruct (Nat.eq_dec i j) as [Heq | Hneq].
  + left. subst. apply OccurP_ref.
  + right. intros H. apply Hneq. apply OccurP_index in H. assumption.
- destruct (Hx i) as [H1 | H1].
  { left. apply OccurP_rator. assumption. }
  destruct (Hy i) as [H2 | H2].
  { left. apply OccurP_rand. assumption. }
  right.
  intros H.
  apply OccurP_app in H.
  tauto.
- destruct (Hx (S i)) as [H | H].
  left. apply OccurP_body. assumption.
  right. intros C. apply OccurP_lam in C. tauto.
Qed.

Lemma OccurP_app_dec {i x y} (H : OccurP i (dB_app x y)) :
  { OccurP i x } + { OccurP i y }.
Proof.
destruct (OccurP_dec x i) as [Hx | Hx].
{ left. assumption. }
destruct (OccurP_dec y i) as [Hy | Hy].
{ right. assumption. }
apply OccurP_app in H.
exfalso.
tauto.
Qed.

Fixpoint occurb (i : nat) (x : dB) : bool :=
  match x with
  | dB_ref j => i =? j
  | dB_app x y => occurb i x || occurb i y
  | dB_lam x => occurb (S i) x
  end.

Lemma occurb_spec x : forall i, reflect (OccurP i x) (occurb i x).
Proof.
induction x as [j | x Hx y Hy | x Hx].
- intros. simpl.
  apply (equivP (P := i = j)).
  { apply Nat.eqb_spec. }
  split.
  + destruct 1. apply OccurP_ref.
  + intros H. apply OccurP_index in H. assumption.
- simpl. intros.
  apply (equivP (P := OccurP i x \/ OccurP i y)).
  { apply orPP; auto. }
  split.
  + destruct 1 as [H | H].
    * apply OccurP_rator. assumption.
    * apply OccurP_rand. assumption.
  + intros H.
    apply OccurP_app in H. assumption.
- simpl. intros. apply (equivP (P := OccurP (S i) x)).
  + apply Hx.
  + split.
    * intros H. apply OccurP_body. assumption.
    * intros. apply OccurP_lam in H. assumption.
Qed.

Definition OccurP_rec
  : forall P : nat -> dB -> Type,
    (forall i : nat, P i (dB_ref i)) ->
    (forall (i : nat) (x y : dB),
    OccurP i x -> P i x -> P i (dB_app x y)) ->
    (forall (i : nat) (x y : dB),
    OccurP i y -> P i y -> P i (dB_app x y)) ->
    (forall (i : nat) (x : dB),
    OccurP (S i) x -> P (S i) x -> P i
    (dB_lam x)) ->
    forall (i : nat) (x : dB), OccurP i x -> P i
    x.
Proof.
  intros.
  assert (E := (proj1 (reflect_iff _ _ (occurb_spec x i)) H)).
  revert i H E.
  induction x; intros j H E. simpl in E.
  - apply (Nat.eqb_eq _ _) in E.
    destruct E.
    apply X.
  - destruct (orb_true_elim _ _ E).
    + assert (OccP_ix1 : OccurP j x1).
      { apply (reflect_iff _ _ (occurb_spec x1 j)).
        exact e. }
      apply X0.
      * apply OccP_ix1.
      * apply IHx1.
        --apply OccP_ix1.
        --exact e.
    + assert (OccP_ix2 : OccurP j x2).
      { apply (reflect_iff _ _ (occurb_spec x2 j)).
        exact e. }
      apply X1.
      * apply OccP_ix2.
      * apply IHx2.
        --apply OccP_ix2.
        --exact e.
  - assert (OccP_Six : OccurP (S j) x).
    { apply (reflect_iff _ _ (occurb_spec x (S j))).
      exact E. }
    apply X2.
    + exact OccP_Six.
    + apply IHx.
      * apply OccP_Six.
      * exact E.
Qed.

Definition OccurP_reindex_inversion x :
  forall i f (Hi : OccurP i (reindex f x)), {j | OccurP j x /\ f j = i}.
Proof.
induction x.
- intros j f Hj.
  simpl in Hj. apply OccurP_index in Hj. subst j.
  exists i.
  split. 2: reflexivity.
  apply OccurP_ref.
- intros. simpl in Hi.
  apply OccurP_app_dec in Hi.
  destruct Hi as [Hi | Hi].
  + destruct (IHx1 i f Hi) as (j, (Hj, Heq)).
    exists j.
    split. 2: exact Heq.
    apply OccurP_rator. assumption.
  + destruct (IHx2 i f Hi) as (j, (Hj, Heq)).
    exists j.
    split. 2: exact Heq.
    apply OccurP_rand. assumption.
- intros.
  simpl in Hi.
  apply OccurP_lam in Hi.
  destruct (IHx (S i) (slide f) Hi) as (j, (Hj, Heq)).
  destruct j as [|j].
  { simpl in Heq. lia. }
  exists j.
  split.
  + apply OccurP_body. assumption.
  + simpl in Heq. lia.
Qed.

Lemma OccurP_lift {j pos δ} (occ_jδp : OccurP j (δ pos))
  : OccurP (S j) (lift δ (S pos)).
Proof.
  simpl.
  apply OccurP_reindex.
  exact occ_jδp.
Qed.

Lemma OccurP_lift_inversion {j pos δ}
(occ : OccurP (S j) (lift δ (S pos)))
: OccurP j (δ pos).
Proof.
  simpl in occ.
  destruct (OccurP_reindex_inversion _ _ _ occ) as [i [occ_jδp e]].
  inversion e; subst.
  exact occ_jδp.
Qed.

Lemma OccurP_subst {j pos : nat} (x: dB) (δ: nat -> dB)
  (occ_jδp : OccurP j (δ pos))
  (occ_px : OccurP pos x)
  : OccurP j (dB_subst δ x).
Proof.
  revert j pos δ occ_jδp occ_px.
  induction x; intros j pos δ occ_jδp occ_px.
  - inversion occ_px; subst.
    exact occ_jδp.
  - inversion occ_px; subst.
    + simpl.
      apply OccurP_rator.
      apply (IHx1 _ _ _ occ_jδp Hx).
    + simpl.
      apply OccurP_rand.
      apply (IHx2 _ _ _ occ_jδp Hy).
  - simpl. apply OccurP_body.
    inversion occ_px; subst.
    eapply IHx.
    + eapply OccurP_lift.
      exact occ_jδp.
    + exact Hy.
Qed.

Lemma OccurP_subst_inversion {j : nat} (x: dB) (δ: nat -> dB)
  (occ_x : OccurP j (dB_subst δ x))
  : {pos & OccurP j (δ pos) /\ OccurP pos x}.
Proof.
  revert j δ occ_x.
  induction x; intros j δ occ_x.
  - simpl in occ_x.
    exists i; split.
    + exact occ_x.
    + constructor.
  - simpl in occ_x.
    destruct (OccurP_app_dec occ_x) as [occ_jx1|occ_jx2].
    + destruct (IHx1 _ _ occ_jx1) as [pos [occ_jδp occ_px1]].
      exists pos.
      split.
      * exact occ_jδp.
      * apply OccurP_rator.
        exact occ_px1.
    + destruct (IHx2 _ _ occ_jx2) as [pos [occ_jδp occ_px2]].
      exists pos.
      split.
      * exact occ_jδp.
      * apply OccurP_rand.
        exact occ_px2.
  - simpl in occ_x.
    dependent induction occ_x.
    destruct (IHx (S i) (lift δ)) as [pos Hp].
    { exact occ_x. }
    destruct pos.
    { destruct Hp as [Hp _].
      simpl in Hp.
      exfalso.
      inversion Hp. }
    exists pos; split.
    + apply OccurP_lift_inversion.
      apply Hp.
    + constructor.
      apply Hp.
Qed.