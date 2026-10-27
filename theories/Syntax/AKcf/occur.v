From CwFdeBruijn.Syntax.AKcf Require Export AKcf.

Inductive Tmcf_OccurP : forall (i:nat) (x : Tmcf), Prop :=
  | Tmcf_OccurP_subst {i:nat} {x} {δ}
      (j:nat) (occ_jx : Tmcf_OccurP j x)
      (occ_ijδ :Tmscf_OccurAtP i j δ)
    : Tmcf_OccurP i (Tmcf_subst x δ)
  | Tmcf_OccurP_π₂ {i} {δ}
      (occ_i0δ : Tmscf_OccurAtP i 0 δ)
    : Tmcf_OccurP i (Tmcf_π₂ δ)
  | Tmcf_OccurP_rator {i} {x y}
      (occ_irator : Tmcf_OccurP i x)
    : Tmcf_OccurP i (Tmcf_app x y)
  | Tmcf_OccurP_rand {i} {x y}
      (occ_irand : Tmcf_OccurP i y)
    : Tmcf_OccurP i (Tmcf_app x y)
  | Tmcf_OccurP_lam {i} {x}
      (occ_ix : Tmcf_OccurP (S i) x)
    : Tmcf_OccurP i (Tmcf_lam x)

with Tmscf_OccurAtP : forall (i pos:nat) (δ: Tmscf), Prop :=
  | Tmscf_OccurAtP_snocπ₂ {i} {δ} {x}
    (occ_ix : Tmcf_OccurP i x)
    : Tmscf_OccurAtP i 0 (Tmscf_snoc δ x)
  | Tmscf_OccurAtP_snocπ₁ {i} {pos} {δ} {x}
    (occ_iδ : Tmscf_OccurAtP i pos δ)
    : Tmscf_OccurAtP i (S pos) (Tmscf_snoc δ x)
  | Tmscf_OccurAtP_id i
    : Tmscf_OccurAtP i i (Tmscf_id)
  | Tmscf_OccurAtP_comp {i pos} {δ₁ δ₂}
    (k:nat) (occ_ikδ₂ : Tmscf_OccurAtP i k δ₂)
    (occ_kjδ₁ : Tmscf_OccurAtP k pos δ₁)
    : Tmscf_OccurAtP i pos (Tmscf_comp δ₁ δ₂)
  | Tmscf_OccurAtP_π₁ {i pos δ}
    (occ_δ : Tmscf_OccurAtP i (S pos) δ)
    : Tmscf_OccurAtP i pos (Tmscf_π₁ δ).

(* NOTE: repetition may arise
  in the output of [[Tmcf_occurences]] and [[Tmscf_occurencesAt]] *)
Fixpoint Tmcf_occurences (x : Tmcf) {struct x} : list nat :=
match x with
  | Tmcf_subst x δ => flat_map (fun occ => Tmscf_occurencesAt occ δ) (Tmcf_occurences x)
  | Tmcf_π₂ δ => Tmscf_occurencesAt 0 δ
  | Tmcf_app x y => (Tmcf_occurences x) ++ (Tmcf_occurences y)
  | Tmcf_lam x => flat_map lpred (Tmcf_occurences x)
end
with Tmscf_occurencesAt (pos:nat) (δ : Tmscf) {struct δ} : list nat :=
match δ with
  | Tmscf_snoc δ x =>
    match pos with
    | 0 => Tmcf_occurences x
    | S (pos') => Tmscf_occurencesAt pos' δ
    end
  | Tmscf_id => (pos :: nil)%list
  | Tmscf_comp δ₁ δ₂ => flat_map (fun occ => Tmscf_occurencesAt occ δ₂) (Tmscf_occurencesAt pos δ₁)
  | Tmscf_π₁ δ => Tmscf_occurencesAt (S pos) δ
end.

Definition Tmcf_Occurb (i:nat) (x:Tmcf) : bool :=
  existsb (Nat.eqb i) (Tmcf_occurences x).
Definition Tmscf_OccurAtb (i pos :nat) (δ:Tmscf) : bool :=
  existsb (Nat.eqb i) (Tmscf_occurencesAt pos δ).

Fixpoint Tmcf_Occur_spec (i:nat) (x:Tmcf)
  : reflect (Tmcf_OccurP i x) (Tmcf_Occurb i x)
with Tmscf_OccurAt_spec (i pos : nat) (δ : Tmscf)
  : reflect (Tmscf_OccurAtP i pos δ) (Tmscf_OccurAtb i pos δ).
Proof.
{ revert i; induction x; intro i.
  - unfold Tmcf_Occurb.
    apply (equivP (in_listnat_spec _ _)).
    simpl.
    rewrite in_flat_map.
    split.
    + simpl.
      intros [pos [In_pos_x In_i_pos_δ]].
      econstructor.
      * apply (Bool.reflect_iff _ _ (IHx pos)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact In_pos_x.
      * apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact In_i_pos_δ.
    + intro H. inversion H.
      split with j; split.
      * apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHx j)).
        exact occ_jx.
      * apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
        exact occ_ijδ.
  - apply (equivP (in_listnat_spec _ _)).
    split.
    + simpl.
      intro H.
      constructor.
      apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
      apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
      exact H.
    + intro H.
      inversion H.
      apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
      apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
      exact occ_i0δ.
  - apply (equivP (in_listnat_spec _ _)).
    split.
    + simpl.
      intros in_app.
      destruct (in_app_or _ _ _ in_app) as [in_rator|in_rand].
      * apply Tmcf_OccurP_rator.
        apply (Bool.reflect_iff _ _ (IHx1 i)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact in_rator.
      * apply Tmcf_OccurP_rand.
        apply (Bool.reflect_iff _ _ (IHx2 i)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact in_rand.
    + intro occ_iapp.
      inversion occ_iapp; subst; cbn.
      * apply in_or_app.
        left.
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHx1 i)).
        exact occ_irator.
      * apply in_or_app.
        right.
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHx2 i)).
        exact occ_irand.
  - apply (equivP (in_listnat_spec _ _)).
    simpl.
    rewrite in_flat_map.
    split.
    + simpl.
      intros [pos [In_pos_x In_i_predpos]].
      destruct pos.
      { inversion In_i_predpos. }
      econstructor.
      apply (Bool.reflect_iff _ _ (IHx (S i))).
      apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
      destruct In_i_predpos as [?|abs].
      -- subst. exact In_pos_x.
      -- exfalso. exact abs.
    + intro H. inversion H.
      split with (S i); split.
      * apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHx (S i))).
        exact occ_ix.
      * simpl. left. reflexivity.
}
{ revert i pos; induction δ; intros i pos.
  - destruct pos.
    + cbn.
      apply (equivP (P:= Tmcf_OccurP i x)).
      * apply Tmcf_Occur_spec.
      * split.
        --intro H. constructor. exact H.
        --intro H. inversion H. exact occ_ix.
    + apply (equivP (in_listnat_spec _ _)).
      simpl.
      split.
      * intro H.
        constructor.
        apply (Bool.reflect_iff _ _ (IHδ i pos)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact H.
      * intro H.
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHδ i pos)).
        inversion H.
        exact occ_iδ.
  - apply (equivP (P:= Nat.eqb i pos)).
    + cbn.
      rewrite Bool.orb_false_r.
      apply idP.
    + split.
      * intro eq_ipos.
        assert (i = pos). {
          apply (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
          exact eq_ipos.
        }
        subst.
        constructor.
      * intro H; inversion H.
        apply (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
        reflexivity.
  - unfold Tmscf_OccurAtb.
    apply (equivP (in_listnat_spec _ _)).
    simpl.
    rewrite in_flat_map.
    split.
    + simpl.
      intros [pos2 [In_pos2posδ1 In_iposδ2]].
      econstructor.
      * apply (Bool.reflect_iff _ _ (IHδ2 i pos2)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact In_iposδ2.
      * apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
        apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        exact In_pos2posδ1.
    + intro H. inversion H.
      split with k; split.
      * apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (IHδ1 k pos)).
        exact occ_kjδ₁.
      * apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
        apply (Bool.reflect_iff _ _ (Tmscf_OccurAt_spec _ _ _)).
        exact occ_ikδ₂.
  - apply (equivP (in_listnat_spec _ _)).
    simpl.
    split.
    + simpl.
      intros In_iSposδ.
      econstructor.
      apply (Bool.reflect_iff _ _ (IHδ i (S pos))).
      apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
      exact In_iSposδ.
    + intro H. inversion H.
      apply (Bool.reflect_iff _ _ (in_listnat_spec _ _)).
      apply (Bool.reflect_iff _ _ (IHδ i (S pos))).
      exact occ_δ.
}
Qed.