From CwFdeBruijn.Syntax.dB Require Export dB depth substLemmas.
From CwFdeBruijn.Syntax.dB Require Import occur TmP equivdBtmTmp depth.
From CwFdeBruijn.Syntax.AKcf Require Export occur_Lemmas context AKcf_Conv Conv_Lemmas context_Lemmas etafun context_minimal.

Fixpoint Tmcf_of_dB (x : dB) {struct x} : Tmcf :=
  match x with
  | dB_ref i   => Tmcf_ref i : Tmcf
  | dB_app x y => Tmcf_app (Tmcf_of_dB x) (Tmcf_of_dB y)
  | dB_lam x   => Tmcf_lam (Tmcf_of_dB x)
  end.

Lemma TmsP_pi1 {p q' δ} (Hδ : TmsP p (S q') δ) :
  TmsP p q' (fun i : nat => δ (S i)).
Proof.
apply AssignP_TmsP.
apply TmsP_AssignP in Hδ.
destruct Hδ as (Hδ1, Hδ2).
split.
- intros. apply Hδ1. lia.
- intros. apply Hδ2. lia.
Qed.

Fixpoint Tmscf_of_Assign' (δ : nat -> dB) (p q : nat) : Tmscf :=
  match q with
  | 0 => cf_iter_π₁ p Tmscf_id
  | S q' => Tmscf_snoc
              (Tmscf_of_Assign' (δ ∘ S) p q')
              (Tmcf_of_dB (δ 0))
  end.

Definition Tmscf_of_Assign {q} (δ : nat -> dB)
  {p} (Hδ : TmsP p q δ)
  : Tmscf
  := recηfun (Tmscf_of_Assign' δ p q).

Definition cfcontext_Tmcf_of_dB {p x} (tmp_px : TmP p x)
  : cfcontext p (Tmcf_of_dB x).
Proof.
  revert p tmp_px.
  induction x as [[i | x y | x]] using dB_depth_wf_rect;
  intros p tmp_px.
  - apply cfcontext_ref.
    inversion tmp_px.
    assumption.
  - simpl.
    apply cfcontext_app.
    + apply H.
      * simpl. lia.
      * inversion tmp_px; assumption.
    + apply H.
      * simpl. lia.
      * inversion tmp_px; assumption.
  - refine (cfcontext_lam _).
    apply (H x).
    + simpl. lia.
    + inversion tmp_px; assumption.
Qed.

Definition cfassign_Tmscf_of_assign {q δ p}
  (Hδ : TmsP p q δ)
  : cfassign p q (Tmscf_of_Assign δ Hδ).
Proof.
  revert δ p Hδ.
  unfold Tmscf_of_Assign.
  induction q; intros δ p Hδ.
  + unfold Tmscf_of_Assign.
    simpl.
    rewrite recηfun_cf_iter_π₁.
    apply cfassign_iter_π₁.
    rewrite Nat.add_0_r.
    apply cfassign_id.
  + unfold Tmscf_of_Assign.
    cbn -[ηfun].
    apply ηfun_cfassign.  
    apply cfassign_snoc.
    - unfold Tmscf_of_Assign in IHq.
      apply IHq.
      apply (TmsP_pi1 Hδ).
    - destruct (TmsP_AssignP Hδ).
      refine (cfcontext_Tmcf_of_dB _).
      apply (proj2 (TmP_iff_ContextP _ _)).
      apply (AssignP_lt 0).
      apply Nat.lt_0_succ.
Qed.

Fixpoint dB_of_Tmcf (x : Tmcf) : dB :=
  match x with
    | Tmcf_subst x δ => dB_subst (assign_of_tmscf δ) (dB_of_Tmcf x)
    | Tmcf_π₂ δ => assign_of_tmscf δ 0
    | Tmcf_app x y => dB_app (dB_of_Tmcf x) (dB_of_Tmcf y)
    | Tmcf_lam x => dB_lam (dB_of_Tmcf x)
  end
  with assign_of_tmscf (δ : Tmscf) : forall  (i : nat), dB :=
    match δ return forall (i : nat), dB with
    | Tmscf_snoc δ x => fun i =>
      match i with
      | 0 => dB_of_Tmcf x
      | S i' => assign_of_tmscf δ i'
      end
    | Tmscf_id => dB_ref
    | Tmscf_comp δ₁ δ₂ => fun i =>
        dB_subst (assign_of_tmscf δ₂) (assign_of_tmscf δ₁ i)
    | Tmscf_π₁ δ => fun i => assign_of_tmscf δ (S i)
  end.

Program Fixpoint AssignPFromTmscf (δ : Tmscf) {p q : nat} (H' : cfassign p q δ) {struct H'}: AssignP p q (assign_of_tmscf δ) :=
  match H' with
    | cfassign_snoc Hδ Hx =>
      let IHδ := (AssignPFromTmscf _ Hδ) in
      let IHx := (ContextPFromTmcf _ Hx) in _
    | cfassign_id p => _
    | cfassign_comp Hδ₁ Hδ₂ =>
      let IHδ₁ := (AssignPFromTmscf _ Hδ₁) in
      let IHδ₂ := (AssignPFromTmscf _ Hδ₂) in _
    | cfassign_π₁ Hδ =>
      let IHδ := (AssignPFromTmscf _ Hδ) in _
  end
  with ContextPFromTmcf (x:Tmcf) {p}
  (H:cfcontext p x) {struct H}: ContextP p (dB_of_Tmcf x) :=
  match H with
    cfcontext_subst Hx Hδ =>
    let IHx := (ContextPFromTmcf _ Hx) in
    let IHδ := (AssignPFromTmscf _ Hδ) in
    _
    | cfcontext_π₂ Hδ =>
      let IHδ := (AssignPFromTmscf _ Hδ) in _
    | cfcontext_app Hx Hy =>
      let IHx := (ContextPFromTmcf _ Hx) in _
    | cfcontext_lam Hx =>
      let IHx := (ContextPFromTmcf _ Hx) in _
  end.

  #[local] Obligation Tactic := idtac.

  Next Obligation.
    intros ? ? ? p ? H ? q δ Hδ x Hx ? ? ? ? IHδ IHx.
    simpl.
    apply AssignP_snoc.
    - exact IHδ.
    - exact IHx.
  Defined.

  Next Obligation.
    intros δ ? q H p ? ? ? ?.
    apply AssignP_id.
  Defined.

  Next Obligation.
    intros ? ? ? p q H r ? δ₁ Hδ₁ ? δ₂ Hδ₂ ? ? ? ? IHδ₁ IHδ₂.
    change (assign_of_tmscf (Tmscf_comp δ₁ δ₂)) with (assign_comp (assign_of_tmscf δ₁) (assign_of_tmscf δ₂)).
      apply (AssignP_comp (q:=r)).
      - exact IHδ₁.
      - exact IHδ₂.
  Defined.

  Next Obligation.
    intros ? ? ? ? ? H p q δ Hδ ? ? ? ? IHδ.
    apply AssignP_π₁.
    exact IHδ.
  Defined.

  (* ContextPFromTmcf *)

  Next Obligation.
    intros ? ? ? p ? q x Hx ? δ Hδ ? ? ? IHx IHδ.
    apply (ContextP_subst _ q).
    + apply IHx.
    + apply IHδ.
  Defined.

  Next Obligation.
    intros ? ? ? p H p0 q δ Hδ ? ? ? ?.
    apply IHδ.
    apply Nat.lt_0_succ.
  Defined.

  Next Obligation.
    intros ? ? ? p H q x y Hx Hy ? ? ? IHx.
    simpl.
    apply ContextP_app.
    + exact IHx.
    + apply ContextPFromTmcf.
      exact Hy.
  Defined.

  Next Obligation.
    intros ? ? ? p H ? x Hx ? ? ? IHx.
    apply ContextP_lam.
    exact IHx.
  Defined.

Definition TmPfromTmcf (x:Tmcf) {p}
(H:cfcontext p x) : TmP p (dB_of_Tmcf x).
Proof.
  apply TmP_iff_ContextP.
  apply ContextPFromTmcf.
  exact H.
Defined.

Lemma TmsPfromTmscf (δ : Tmscf) {p q : nat} (H : cfassign p q δ) : TmsP p q (assign_of_tmscf δ).
Proof.
  apply AssignP_TmsP.
  apply AssignPFromTmscf.
  exact H.
Qed.

Lemma assign_of_tmscf_id : assign_of_tmscf Tmscf_id = dB_ref.
Proof.
  reflexivity.
Qed.

Lemma assign_of_tmscf_iter_π₁ δ j : assign_of_tmscf (cf_iter_π₁ j δ) = fun i => assign_of_tmscf δ (j + i).
Proof.
  revert δ.
  induction j; intro δ.
  + reflexivity.
  + simpl.
    fold cf_iter_π₁.
    rewrite (IHj δ).
    apply extensionality; intro i.
    f_equal.
    apply Nat.add_succ_r.
Defined.

Theorem dBTmcf_immersion (x:dB) : (dB_of_Tmcf (Tmcf_of_dB x)) = x.
Proof.
  induction x as [[i|x y| x]] using dB_depth_wf_rect.
  - simpl.
    rewrite assign_of_tmscf_iter_π₁.
    simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - simpl.
    rewrite H.
    + f_equal.
      apply H.
      simpl. lia.
    + simpl. lia.
  - simpl.
    f_equal.
    apply H.
    simpl. lia.
Defined.

Local Definition add i := fun n => n + i.

Lemma assignTmscf_immersion_ref (k p : nat)
  : assign_of_tmscf (Tmscf_of_Assign' (dB_ref ∘ (add k)) (add k p) p) = dB_ref ∘ (add k).
Proof.
  revert k.
  induction p; intros k.
  { cbn.
    rewrite assign_of_tmscf_iter_π₁.
    apply extensionality.
    intro x.
    cbn.
    unfold add, compose.
    f_equal. lia. }

  apply extensionality.
  intro x.
  destruct x.
  { cbn.
    rewrite assign_of_tmscf_iter_π₁.
    cbn.
    unfold add, compose.
    f_equal. lia. }

  eapply eq_trans; [eapply eq_trans| idtac].
  2: { exact (equal_f (IHp (S k)) x). }
  - cbn.
    f_equal.
    f_equal.
    + apply extensionality.
      intro y.
      unfold add, compose. f_equal. lia.
    + unfold add. lia.
  - unfold add, compose. f_equal. lia.
Qed.

Lemma assign_of_tmscf_ηfun {δ}
  : assign_of_tmscf (ηfun δ) = assign_of_tmscf δ.
Proof.
  destruct δ; try (cbn; reflexivity).
  cbn.
  destruct (reflect_dec _ _ (etaRelated_spec δ x)).
  - rewrite (introT (etaRelated_spec _ _) e).
    destruct δ; try (cbn; reflexivity).
    apply extensionality; intros [| ?  ].
    + rewrite (etaRelatedP_Tmcf_eq e).
      reflexivity. 
    + reflexivity.
  - rewrite (introF (etaRelated_spec _ _) n).
    reflexivity.
Qed.

Lemma assign_of_tmscf_recηfun {δ}
  : assign_of_tmscf (recηfun δ) = assign_of_tmscf δ.
Proof.
  induction δ; try (cbn; reflexivity).
  cbn -[ηfun].
  rewrite assign_of_tmscf_ηfun.
  cbn.
  rewrite IHδ.
  reflexivity.
Qed.

Theorem TmsPTmscf_immersion {p q} (δ: nat -> dB) (H:TmsP p q δ)
: assign_of_tmscf (Tmscf_of_Assign δ H) = δ.
Proof.
  unfold Tmscf_of_Assign.
  rewrite assign_of_tmscf_recηfun.
  induction H.
  - apply assign_of_tmscf_iter_π₁.
  - apply extensionality.
    intro i.
    destruct i.
    + apply dBTmcf_immersion.
    + simpl.
      rewrite snoc_δ_S.
      apply (f_equal (fun f => f i)).
      apply IHTmsP.
  - eapply eq_trans; [eapply eq_trans| idtac].
    2: { exact (assignTmscf_immersion_ref 0 p). }
    + f_equal.
      f_equal.
      all: unfold add, compose.
      * apply extensionality.
        intro. f_equal. lia.
      * lia.
    + apply extensionality.
      unfold add, compose.
      intro. f_equal. lia.
  - unfold assign_comp at 2.
    revert q δ₁ H p δ₂ H0 IHTmsP1 IHTmsP2.
    induction r; intros q δ₁ H p δ₂ H0 IHTmsP1 IHTmsP2.
    { cbn in *.
      rewrite assign_of_tmscf_iter_π₁ in *.
      cbn in *.
      destruct (TmsP_AssignP H0).
      subst.
      apply extensionality. intro x.
      cbn.
      specialize (AssignP_ge (q + x)).
      symmetry.
      eapply eq_trans.
      - apply AssignP_ge.
        lia.
      - f_equal.
        lia. }
    apply extensionality.
    intro x.
    cbn.
    destruct x.
    { rewrite dBTmcf_immersion.
      reflexivity. }
    refine (equal_f (IHr _ (δ₁ ∘ S) _ p δ₂ H0 _ IHTmsP2) x).
    + apply (TmsP_π₁ _ H).
    + apply extensionality; intro x'.
      apply (equal_f IHTmsP1 (S x')).
  - unfold assign_π₁ at 2.
    revert p δ H IHTmsP.
    induction q; intros p δ H IHTmsP.
    { cbn.
      rewrite assign_of_tmscf_iter_π₁.
      destruct (TmsP_AssignP H).
      apply extensionality.
      intro i.
      symmetry.
      eapply eq_trans.
      - apply AssignP_ge.
        lia.
      - cbn. f_equal. lia. }
    apply extensionality.
    intro x.
    destruct x.
    { cbn.
      rewrite dBTmcf_immersion.
      reflexivity. }
    cbn.
    unfold assign_π₁.
    refine (equal_f (IHq _ (δ ∘ S) _ _) x).
    + apply (TmsP_π₁ _ H).
    + apply extensionality; intro x'.
      apply (equal_f IHTmsP (S x')).
Defined.

Fixpoint TmcfOccur_soundness {i:nat} (x:Tmcf)
  (occ_x : Tmcf_OccurP i x)
  : OccurP i (dB_of_Tmcf x)
with TmscfOccur_soundness {i pos:nat} (δ: Tmscf)
  (Occ_i : Tmscf_OccurAtP i pos δ)
  : OccurP i (assign_of_tmscf δ pos).
Proof.
{ dependent induction occ_x;
    subst.
  - simpl.
    apply (OccurP_subst (pos := j)).
    + apply (TmscfOccur_soundness i j δ occ_ijδ).
    + exact IHocc_x.
  - simpl.
    apply (TmscfOccur_soundness i 0 δ occ_i0δ).
  - simpl.
    apply OccurP_rator.
    exact IHocc_x.
  - simpl.
    apply OccurP_rand.
    exact IHocc_x.
  - simpl.
    apply OccurP_body.
    exact IHocc_x.
}
{ dependent induction Occ_i.
  - simpl.
    apply (TmcfOccur_soundness i x occ_ix).
  - simpl.
    exact IHOcc_i.
  - simpl.
    constructor.
  - simpl.
    apply (OccurP_subst (pos:=k)).
    + apply IHOcc_i1.
    + apply IHOcc_i2.
  - simpl.
    apply (TmscfOccur_soundness i (S pos) δ Occ_i).
}
Qed.

Lemma TmcfOccur_completeness' {i:nat} (x:dB)
  (occ_x : OccurP i x)
  : Tmcf_OccurP i (Tmcf_of_dB x).
Proof.
  revert i occ_x.
  induction x using dB_depth_wf_rect.
  intros i occ_x.
  destruct occ_x.
  - simpl.
    constructor.
    assert (e : (i = i + 0)). { lia. } rewrite e at 1.
    apply Tmscf_OccurAtP_cf_iter_π₁.
  - simpl.
    apply Tmcf_OccurP_rator.
    apply H.
    + simpl. lia.
    + exact occ_x.
  - simpl.
    apply Tmcf_OccurP_rand.
    apply H.
    + simpl. lia.
    + exact occ_x.
  - simpl.
    constructor.
    apply H.
    * simpl. lia.
    * exact occ_x.
Qed.

Fixpoint TmcfOccur_completeness {i:nat} (x:Tmcf)
  (occ_x : OccurP i (dB_of_Tmcf x))
  : Tmcf_OccurP i x
with TmscfOccur_completeness {i pos:nat} (δ: Tmscf)
  (occ_iδp : OccurP i ((assign_of_tmscf δ) pos))
  : Tmscf_OccurAtP i pos δ.
Proof.
{
  revert i occ_x.
  induction x; intros i occ_x; simpl in occ_x.
  - destruct (OccurP_subst_inversion _ _ occ_x) as [pos [occ_iδp occ_px]].
    econstructor.
    + apply IHx.
      exact occ_px.
    + apply (TmscfOccur_completeness _ _ _ occ_iδp).
  - constructor.
    apply (TmscfOccur_completeness _ _ _ occ_x).
  - inversion occ_x; subst.
    + apply Tmcf_OccurP_rator.
      apply IHx1.
      exact Hx.
    + apply Tmcf_OccurP_rand.
      apply IHx2.
      exact Hy.
  - constructor.
    apply IHx.
    inversion occ_x; subst.
    exact Hy.
}
{
  revert i pos occ_iδp.
    induction δ; intros i pos occ_iδp;
    simpl in occ_iδp.
  - destruct pos.
    + constructor.
      apply TmcfOccur_completeness.
      exact occ_iδp.
    + constructor.
      apply IHδ.
      exact occ_iδp.
  - inversion occ_iδp; subst.
    constructor.
  - destruct (OccurP_subst_inversion _ _ occ_iδp) as [j [occi_δ₂j occj_δ₁p]].
    econstructor.
    + apply IHδ2.
      exact occi_δ₂j.
    + apply IHδ1.
      exact occj_δ₁p.
  - constructor.
    apply IHδ.
    exact occ_iδp. }
Qed.

Open Scope AKcf.

Lemma Tmcfσsoundness'' {x y : Tmcf} (red: Tmcfσstep' x y)
  : dB_of_Tmcf x = dB_of_Tmcf y.
Proof.
  dependent induction red; try reflexivity.
  - simpl.
    rewrite dB_subst_subst.
    reflexivity.
  - simpl.
    f_equal.
    f_equal.
    apply extensionality; intros [|i]; try reflexivity.
    change (dB.lift (assign_of_tmscf δ) (S i) =
      dB_subst (dB_ref ∘ S) (assign_of_tmscf δ i)).
    rewrite <- reindexisasubst.
    change (((dB.lift (assign_of_tmscf δ)) ∘ S) i =
      (reindex S ∘ (assign_of_tmscf δ)) i).
    rewrite (liftS (δ:=(assign_of_tmscf δ))).
    reflexivity.
Qed.

Lemma Tmscfσsoundness'' {δ σ : Tmscf} (red: Tmscfσstep' δ σ)
  : assign_of_tmscf δ = assign_of_tmscf σ.
Proof.
  dependent induction red; try reflexivity.
  - simpl.
    rewrite dB_ref_Id'.
    reflexivity.
  - simpl.
    apply extensionality.
    intro i.
    rewrite dB_subst_subst.
    reflexivity.
  - apply extensionality; intros [|i]; reflexivity.
  - apply extensionality; intros [|i]; reflexivity.
Qed.

Fixpoint Tmcfσsoundness' {x y : Tmcf} (red: x --> y) {struct red}
  : dB_of_Tmcf x = dB_of_Tmcf y
with Tmscfσsoundness' {δ σ : Tmscf} (red: δ --s> σ) {struct red}
  : assign_of_tmscf δ = assign_of_tmscf σ.
Proof.
{ inversion red.
  - apply (Tmcfσsoundness'' H).
  - simpl.
    f_equal.
    apply (Tmcfσsoundness' _ _ H).
  - simpl.
    f_equal.
    apply (Tmscfσsoundness' _ _ H).
  - simpl.
    apply (f_equal (fun f => f 0)).
    apply (Tmscfσsoundness' _ _ H).
  - simpl.
    f_equal.
    apply (Tmcfσsoundness' _ _ H).
  - simpl. f_equal.
    apply (Tmcfσsoundness' _ _ H).
  - simpl. f_equal.
    apply (Tmcfσsoundness' _ _ H).
}
{ inversion red.
  - apply (Tmscfσsoundness'' H).
  - simpl. rewrite (Tmscfσsoundness' _ _ H). reflexivity.
  - simpl. rewrite (Tmcfσsoundness' _ _ H). reflexivity.
  - simpl. rewrite (Tmscfσsoundness' _ _ H). reflexivity.
  - simpl. rewrite (Tmscfσsoundness' _ _ H). reflexivity.
  - simpl. rewrite (Tmscfσsoundness' _ _ H). reflexivity.
}
Qed.

Lemma Tmcfσsoundness {x y : Tmcf} (red: x -->* y)
  : dB_of_Tmcf x = dB_of_Tmcf y.
Proof.
  induction red.
  - apply (Tmcfσsoundness' H).
  - reflexivity.
  - exact (eq_trans IHred1 IHred2).
Qed.

Lemma Tmscfσsoundness {δ σ : Tmscf} (red: δ --s>* σ)
  : assign_of_tmscf δ = assign_of_tmscf σ.
Proof.
  induction red.
  - apply (Tmscfσsoundness' H).
  - reflexivity.
  - exact (eq_trans IHred1 IHred2).
Qed.

Lemma TmcfDB_immersion_V {x: Tmcf} (xV: Tmcfσvalue x)
  : Tmcf_of_dB (dB_of_Tmcf x) = x.
Proof.
  induction xV; simpl.
  - simpl.
    destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [i ?]; subst.
    rewrite assign_of_tmscf_iter_π₁, Nat.add_0_r.
    reflexivity.
  - simpl.
    f_equal; assumption.
  - f_equal. exact IHxV.
Qed.

Lemma TmcfDB_immersion (x: Tmcf)
  : x -->* Tmcf_of_dB (dB_of_Tmcf x).
Proof.
  destruct (Tmcf_normalization x) as [x0 [xred x0nf]].
  eapply rt_trans.
  - exact xred.
  - erewrite (Tmcfσsoundness).
    + rewrite TmcfDB_immersion_V.
      * apply rt_refl.
      * apply Tmcfσnf_is_value.
        exact x0nf.
    + exact xred.
Qed.

Lemma recηfun_Tmscf_of_Assign' {p q δ} (Hδ : TmsP p q δ)
  : recηfun (Tmscf_of_Assign' δ p q) = recηfun (Tmscf_of_Assign' δ (S p) (S q)).
Proof.
  apply TmsP_AssignP in Hδ.
  revert p δ Hδ.
  induction q; intros p δ Hδ. 
  - cbn-[recηfun].
    destruct Hδ.
    rewrite recηfun_cf_iter_π₁.
    rewrite (AssignP_ge 0). 2:{lia. }
    assert ( p-0 = p ). {lia. } 
    cbn. rewrite H.
    rewrite ifT. {reflexivity. }
    apply (introT (Tmscf_eq_spec _ _)).
    reflexivity.
  - cbn-[recηfun].
    unfold recηfun.
    f_equal.
    f_equal.
    fold recηfun.
    eapply eq_trans. {
      apply (IHq p (δ ∘ S)).
      destruct Hδ.
      split.
      - intros i lt. apply (AssignP_lt). lia.
      - intros i le. apply (AssignP_ge). lia. }
    reflexivity.
Qed.

Lemma TmscfDB_immersion_V {δ : Tmscf} {p q} (ass : cfassign p q δ) (δV: Tmscfσvalue δ)
  : (recηfun (Tmscf_of_Assign' (assign_of_tmscf δ) p q)) = δ.
Proof.
  revert p ass.
  induction δV; intros p ass.
  - destruct (cfassign_cf_iter_π₁idP δ ass Hδ) as [le ?]; subst.
    rewrite assign_of_tmscf_iter_π₁.
    rewrite assign_of_tmscf_id.
    clear Hδ.
    clear ass.
    induction q.
    { cbn.
      rewrite recηfun_cf_iter_π₁.
      f_equal.
      lia. }
    cbn -[ηfun].
    assert (e:(fun i : nat => dB_ref (p - S q + i)) ∘ S
              =fun i : nat => dB_ref (p - q + i)).
    { apply extensionality. intro. unfold compose.  f_equal. lia. }
    rewrite e.
    rewrite IHq. 2: { lia. }
    cbn.
    assert (etaRelatedb (cf_iter_π₁ (p - q) Tmscf_id) (Tmcf_ref (p - S q + 0))).
    { assert (E : p-q = S (p - q -1)). { lia. } rewrite E. simpl.
      apply (introT (Tmscf_eq_spec _ _)).
      unfold cf_iter_π₁.
      f_equal.
      lia. }
    rewrite H.
    assert (E : p-q = S (p - q -1)). { lia. } rewrite E. simpl.
    unfold cf_iter_π₁.
    f_equal.
    lia.
  - inversion ass; subst.
    cbn -[assign_of_tmscf].
    assert (E:(assign_of_tmscf (Tmscf_snoc δ x) ∘ S) = assign_of_tmscf δ). {
      apply extensionality.
      intros [|i ]; reflexivity.
    }
    rewrite E.
    assert (EE: recηfun (Tmscf_of_Assign' (assign_of_tmscf δ) p q0) = δ).
    {
      eapply eq_trans.
      2:{ apply (IHδV (S p)).
          apply (cfassign_weakening' Hδ 1). }
      apply recηfun_Tmscf_of_Assign'.
      apply (TmsPfromTmscf _ Hδ).
    }
    rewrite EE.
    cbn-[etaRelatedb].
    rewrite (TmcfDB_immersion_V Hx).
    rewrite ifF. { reflexivity. }
    apply (introF (etaRelated_spec _ _) Hη).
Qed.

Lemma TmscfDB_immersion {p q} (δ : Tmscf) (ass : cfassign p q δ)
  : δ --s>* Tmscf_of_Assign (assign_of_tmscf δ) (TmsPfromTmscf δ ass).
Proof.
  destruct (Tmscf_normalization δ) as [δ0 [δred δ0nf]].
  eapply rt_trans.
  - exact δred.
  - unfold Tmscf_of_Assign.
    rewrite (Tmscfσsoundness δred).
    + rewrite TmscfDB_immersion_V.
      * apply rt_refl.
      * apply (cfassign_preserved δred ass).
      * apply Tmscfσnf_is_value.
        exact δ0nf.
Qed.

Lemma Tmscf_nf_uniqueness
  (δ σ τ : Tmscf) (σ_nf : normal_form Tmscfσstep σ) (τ_nf : normal_form Tmscfσstep τ)
  (δredσ : δ --s>* σ)
  (δredτ : δ --s>* τ)
  : σ = τ.
Proof.
  assert (E : assign_of_tmscf σ = assign_of_tmscf τ).
  { eapply eq_trans with (assign_of_tmscf δ).
    - symmetry.
      apply (Tmscfσsoundness δredσ).
    - apply (Tmscfσsoundness δredτ).
  }
  erewrite <-(TmscfDB_immersion_V  (cfassign_preserved δredσ (Minass_ass δ)) (Tmscfσnf_is_value σ σ_nf)).
  erewrite <-(TmscfDB_immersion_V  (cfassign_preserved δredτ (Minass_ass δ)) (Tmscfσnf_is_value τ τ_nf)).
  destruct E.
  reflexivity.
Qed.