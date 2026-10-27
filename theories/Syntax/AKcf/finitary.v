From CwFdeBruijn.Syntax.AKcf Require Import AKcf AKcf_Conv substid GenRewr values context equivContextOccur longSnoc normalization.

Require Import Setoid Morphisms RelationClasses.
Require Import ssrfun.

Open Scope AKcf.

Definition Tmcf_isSupport n (a:Tmcf) :=
  forall (δ1 δ2:Tmscf) (v : Vector.t Tmcf n),
    Tmcf_subst a (AKcf_longsnoc δ1 v) <-->* Tmcf_subst a (AKcf_longsnoc δ2 v).

Definition Tmscf_isPreSupport (m n : nat) (δ:Tmscf) :=
  cf_iter_π₁ n δ --s>* cf_iter_π₁ m id.
Definition Tmscf_isSupport (m n : nat) (δ:Tmscf) :=
  (Tmscf_isPreSupport m n δ) /\
  forall i, i<n -> Tmcf_isSupport m (cf_iter_π₂ i δ).

Section Compatibility.
  Global Instance Tmcf_isSupport_σstep_impl {n}
  : Proper (Tmcfσstep ==> impl) (@Tmcf_isSupport n).
  Proof.
    intros ? ? ? H ? ? ?.
    unfold Tmcf_isSupport.
    rewrite <-H0.
    apply H.
  Qed.
  Global Instance Tmcf_isSupport_σstep_flipimpl {n}
  : Proper (Tmcfσstep ==> flip impl) (@Tmcf_isSupport n).
  Proof.
    intros ? ? ? ?.
    unfold Tmcf_isSupport.
    intros ? ? ?.
    rewrite H.
    apply H0.
  Qed.
  Global Instance Tmcf_isSupport_σconv_impl {n}
  : Proper (Tmcfσconv ==> impl) (@Tmcf_isSupport n) :=
  rt_lift_proper_1' _ Tmcf_isSupport_σstep_impl.
  Global Instance Tmcf_isSupport_σconv_flipimpl {n}
  : Proper (Tmcfσconv ==> flip impl) (@Tmcf_isSupport n) :=
  rt_lift_proper_1' _ Tmcf_isSupport_σstep_flipimpl.
  Global Instance Tmcf_isSupport_σeq_impl {n}
  : Proper (Tmcfσeq ==> impl) (@Tmcf_isSupport n).
  Proof.
    intros ? ? ? H ? ? ?.
    unfold Tmcf_isSupport.
    rewrite <-H0.
    apply H.
  Qed.
  Global Instance Tmcf_isSupport_σeq_flipimpl {n}
  : Proper (Tmcfσeq ==> flip impl) (@Tmcf_isSupport n).
  Proof.
    intros ? ? ? H ? ? ?.
    unfold Tmcf_isSupport.
    rewrite H0.
    apply H.
  Qed.

  Global Instance Tmscf_isPreSupport_σstep_impl {m n}
  : Proper (Tmscfσstep ==> impl) (@Tmscf_isPreSupport m n).
  Proof.
    intros ? ? H H0.
    unfold Tmscf_isPreSupport in *.
    unshelve eapply (Tmscfσstep_bwtr _ H0).
    { apply Tmcfσnf_cf_iter_π₁id. }
    now rewrite H.
  Qed.
  Global Instance Tmscf_isPreSupport_σstep_flipimpl {m n}
  : Proper (Tmscfσstep ==> flip impl) (@Tmscf_isPreSupport m n).
  Proof.
    intros ? ? H H0.
    unfold Tmscf_isPreSupport in *.
    rewrite H.
    apply H0.
  Qed.
  Global Instance Tmscf_isPreSupport_σconv_impl {m n}
  : Proper (Tmscfσconv ==> impl) (@Tmscf_isPreSupport m n) :=
  rt_lift_proper_1' _ Tmscf_isPreSupport_σstep_impl.
  Global Instance Tmscf_isPreSupport_σconv_flipimpl {m n}
  : Proper (Tmscfσconv ==> flip impl) (@Tmscf_isPreSupport m n) :=
  rt_lift_proper_1' _ Tmscf_isPreSupport_σstep_flipimpl.

  Global Instance Tmscf_isSupport_σstep_impl {m n}
  : Proper (Tmscfσstep ==> impl) (@Tmscf_isSupport m n).
  Proof.
    intros ? ? ? H.
    unfold Tmscf_isSupport.
    split.
    + rewrite <-H0. apply H.
    + intros ? le. rewrite <-H0. apply H. exact le.
  Qed.
  Global Instance Tmscf_isSupport_σstep_flipimpl {m n}
  : Proper (Tmscfσstep ==> flip impl) (@Tmscf_isSupport m n).
  Proof.
    intros ? ? ? H.
    unfold Tmscf_isSupport.
    split.
    + rewrite H0. apply H.
    + intros ? le. rewrite H0. apply H. exact le.
  Qed.
  Global Instance Tmscf_isSupport_σconv_impl {m n}
  : Proper (Tmscfσconv ==> impl) (@Tmscf_isSupport m n) :=
  rt_lift_proper_1' _ Tmscf_isSupport_σstep_impl.
  Global Instance Tmscf_isSupport_σconv_flipimpl {m n}
  : Proper (Tmscfσconv ==> flip impl) (@Tmscf_isSupport m n) :=
  rt_lift_proper_1' _ Tmscf_isSupport_σstep_flipimpl.
End Compatibility.

Section Lemmas.

  Lemma cf_iter_π₁_iter_snoc {i a δ}
    : cf_iter_π₁ i (iter (Tmscf_snoc^~ a) i δ) --s>* δ.
  Proof.
    induction i.
    - reflexivity.
    - rewrite cf_iter_π₁_flip.
      cbn.
      rewrite cf_π₁beta.
      apply IHi.
  Qed.

  Lemma Tmcf_support_ref_to_lt {n i} (H:Tmcf_isSupport n (Tmcf_ref i))
    : i<n.
  Proof.
    destruct (Nat.lt_ge_cases i n); [assumption|exfalso].
    set (δ1 := (iter (Tmscf_snoc ^~ (Tmcf_ref 0)) (i - n) id)).
    set (δ2 := (iter (Tmscf_snoc ^~ (Tmcf_ref 0)) (i - n) (π1 id))).
    assert (Tmcf_ref 0 <-->* Tmcf_ref 1).
    { etransitivity;[symmetry|etransitivity].
      2: apply (H δ1 δ2).
      all: rewrite Tmscf_substref.
      all: rewrite AKcf_jth_longsnoc_ge; [|lia].
      all: unfold cf_iter_π₂.
      all: unfold δ1, δ2; rewrite cf_iter_π₁_iter_snoc.
      all: reflexivity. }
    assert (abs: not (Tmcf_ref 0 = Tmcf_ref 1)) by discriminate; apply abs.
    rewrite <-(@nffun_Tmcf_ref 0), <-(@nffun_Tmcf_ref 1).
    apply (proj2 (nfuniqueness_iff_conv Tmcf_nf_uniqueness Tmcf_normalization (Tmcf_ref 0) (Tmcf_ref 1) )).
    exact H1.
    Unshelve.
    apply (Vector.const (Tmcf_ref 0)).
  Qed.

  (* The proof for this uses normalization, since
  it is not true that being an app is reflected by the reduction relation
  (π2 ⟨δ,a@b⟩ --> a@b) *)
  Lemma Tmcfσeq_to_rator {a' b' a b} (H: a' @ b' <-->* a @ b)
    : a' <-->* a.
  Proof.
    set (e := (proj2 (nfuniqueness_iff_conv
      Tmcf_nf_uniqueness Tmcf_normalization (a' @ b') (a @ b)) H)).
    set (e2 := (eq_trans (eq_trans
      (eq_sym (@nffun_Tmcf_app a' b'))
      e)
      (@nffun_Tmcf_app a b))).
    inversion e2.
    etransitivity;[etransitivity|].
    + rewrite (nffun_conv (Tmcf_normalization a')); reflexivity.
    + rewrite H1; reflexivity.
    + rewrite <-(nffun_conv (Tmcf_normalization a)); reflexivity.
  Qed.
  Lemma Tmcfσeq_to_rand {a' b' a b} (H: a' @ b' <-->* a @ b)
    : b' <-->* b.
  Proof.
    set (e := (proj2 (nfuniqueness_iff_conv
      Tmcf_nf_uniqueness Tmcf_normalization (a' @ b') (a @ b)) H)).
    set (e2 := (eq_trans (eq_trans
      (eq_sym (@nffun_Tmcf_app a' b'))
      e)
      (@nffun_Tmcf_app a b))).
    inversion e2.
    etransitivity;[etransitivity|].
    + rewrite (nffun_conv (Tmcf_normalization b')); reflexivity.
    + rewrite H2; reflexivity.
    + rewrite <-(nffun_conv (Tmcf_normalization b)); reflexivity.
  Qed.
  Lemma Tmcf_support_from_app {n} {a b:Tmcf}
    (H : Tmcf_isSupport n (a @ b)) :
    (Tmcf_isSupport n a) /\
    (Tmcf_isSupport n b).
  Proof.
    esplit.
    - intros δ1 δ2 v.
      set (eq := (H δ1 δ2 v)).
      rewrite !cf_appsubst in eq.
      apply (Tmcfσeq_to_rator eq).
    - intros δ1 δ2 v.
      set (eq := (H δ1 δ2 v)).
      rewrite !cf_appsubst in eq.
      apply (Tmcfσeq_to_rand eq).
  Qed.

  Lemma Tmcf_support_from_lam {n} {a:Tmcf}
    (H : Tmcf_isSupport n (λ a)) :
    (Tmcf_isSupport (S n) a).
  Proof.
    intros δ1 δ2 v.

    assert (e:=(H δ1 δ2 (VectorDef.tl v))).
    rewrite !cf_lamsubst in e.
    apply Tmcfσeq_from_lam in e.
    unshelve eassert (ee:=(Tmcf_subst_σeq _ _ e ⟨id,VectorDef.hd v⟩ ⟨id,VectorDef.hd v⟩ _)).
    {reflexivity. }
    clear e.
    rewrite !cf_substsubst in ee.
    rewrite !AKcf_lift_longsnoc, !AKcf_longsnocomp in ee.
    rewrite !cf_ass in ee.
    rewrite !cf_compπ₁id, !cf_π₁beta, !cf_idr in ee.
    simpl in ee.
    rewrite !cf_substπ₂, !cf_idl, !cf_π₂beta in ee.
    rewrite !Vector.map_map in ee.
    assert (
      forall n (v:Vector.t Tmcf n) (y:Tmcf),
      Tmcfvecσeq
      (VectorDef.map
        (fun x : Tmcf => (x [π1 id]) [⟨ id, y ⟩])
        v)
      (VectorDef.map
        (fun x => x)
        v)).
    { intros.
      unfold Tmcfvecσconv.
      induction v0.
      - cbn. reflexivity.
      - cbn.
        apply Vector.Forall2_cons.
        + now rewrite cf_substsubst, cf_π₁comp, cf_idl, cf_π₁beta, subst_id.
        + exact IHv0.
    }
    rewrite (H0 n (VectorDef.tl v) (VectorDef.hd v)) in ee.
    rewrite VectorSpec.map_id in ee.
    rewrite (VectorSpec.eta v).
    exact ee.
  Qed.

  Lemma Tmcf_support_of_app {n} {a b:Tmcf}
    (Ha : Tmcf_isSupport n a)
    (Hb : Tmcf_isSupport n b)
    : Tmcf_isSupport n (a @ b).
  Proof.
    intros δ1 δ2 v.
    rewrite !cf_appsubst.
    rewrite (Ha δ1 δ2 v).
    rewrite (Hb δ1 δ2 v).
    reflexivity.
  Qed.

  Lemma Tmcf_support_of_lam {n} {a}
    (Ha : Tmcf_isSupport (S n) a)
    : Tmcf_isSupport n (λ a).
  Proof.
    intros δ1 δ2 v.
    rewrite !cf_lamsubst.
    apply Tmscf_lam_σeq.
    rewrite !AKcf_lift_longsnoc.
    apply Ha.
  Qed.

End Lemmas.

(* For AKcf terms, [cfcontext] implies [Tmcf_isSupport] *)
Section cfcontext_to_Tmcf_isSupport.
Lemma cfcontext_to_Tmcf_isSupport_values (a:Tmcf) n
  (isV : Tmcfσvalue a) (H : cfcontext n a)
  : Tmcf_isSupport n a.
Proof.
  revert n H; induction isV; intros n H.
  - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [j ?]; subst.
    intros δ1 δ2 v.
    change (Tmcf_π₂ (cf_iter_π₁ j Tmscf_id)) with (Tmcf_ref j).
    rewrite !Tmscf_substref.
    inversion H; subst.
    destruct (cfassign_cf_iter_π₁idP _  Hδ0 Hδ).
    assert (jleqì := cf_iter_π₁id_inj H1).
    assert (j <= n) by lia.
    rewrite !(AKcf_jth_longsnoc_le).
    erewrite Vector.nth_order_ext.
    reflexivity.
    Unshelve. all: lia.
  - inversion H; subst.
    apply Tmcf_support_of_app.
    + apply (IHisV1 _ Hx).
    + apply (IHisV2 _ Hy).
  - inversion H; subst.
    apply Tmcf_support_of_lam.
    apply (IHisV _ H2).
Qed.

Theorem cfcontext_to_Tmcf_isSupport (a:Tmcf) n
  (H : cfcontext n a)
  : Tmcf_isSupport n a.
Proof.
  destruct (Tmcf_normalization a) as [anf [ared anf_is]].
  intros ? ? ?.
  rewrite ared.
  apply cfcontext_to_Tmcf_isSupport_values.
  - exact (Tmcfσnf_is_value anf_is).
  - exact (cfcontext_preserved ared H).
Qed.
End cfcontext_to_Tmcf_isSupport.

(* The converse hold only for values:
  For AKcf values, [Tmcf_isSupport] implies [cfcontext] *)
Theorem Tmcf_isSupport_to_cfcontext_values (a:Tmcf) n
  (isV : Tmcfσvalue a)
  (H : Tmcf_isSupport n a)
  : cfcontext n a.
Proof.
  revert n H; induction isV; intros n H.
  - destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ); subst.
    assert (le:= Tmcf_support_ref_to_lt H).
    apply (cfcontext_π₂ (q:= n - x - 1)).
    apply cfassign_iter_π₁.
    assert (e:((x + S (n - x - 1)) = n)) by lia.
    rewrite e.
    constructor.
  - destruct (Tmcf_support_from_app H).
    constructor.
    + apply IHisV1; assumption.
    + apply IHisV2; assumption.
  - apply cfcontext_lam.
    apply IHisV.
    exact (Tmcf_support_from_lam H).
Qed.

(* For AKcf terms, [cfassign] implies [Tmscf_isSupport] *)
Section cfassign_to_Tmscf_isSupport.
Lemma cfassign_to_Tmscf_isPreSupport_values (δ:Tmscf) m n
  (isV : Tmscfσvalue δ) (H : cfassign m n δ)
  : Tmscf_isPreSupport m n δ.
Proof.
  revert m n H; induction isV; intros m n H.
  - destruct (cfassign_cf_iter_π₁idP _ H Hδ) as [ge e].
    rewrite e; clear e.
    unfold Tmscf_isPreSupport.
    unshelve erewrite <-cf_iter_π₁_split.
    2: reflexivity.
    lia.
  - destruct n.
    { exfalso. apply (contextof_snoc_false H). }
    unfold Tmscf_isPreSupport.
    rewrite cf_iter_π₁_flip.
    rewrite cf_π₁beta.
    apply (IHisV _ _ (assignof_snoc H)).
Qed.
Lemma cfassign_to_Tmscf_isPreSupport (δ:Tmscf) {m n}
  (H : cfassign m n δ)
  : Tmscf_isPreSupport m n δ.
Proof.
  destruct (Tmscf_normalization δ) as [δnf [δred δnf_is]].
  rewrite δred.
  apply cfassign_to_Tmscf_isPreSupport_values.
  - exact (Tmscfσnf_is_value _ δnf_is).
  - exact (cfassign_preserved δred H).
Qed.
Lemma cfassign_to_Tmscf_isSupport_values (δ:Tmscf) m n
  (isV : Tmscfσvalue δ) (H : cfassign m n δ)
  : Tmscf_isSupport m n δ.
Proof.
  split; [apply cfassign_to_Tmscf_isPreSupport_values;assumption|].
  revert m n H; induction isV; intros m n H i le.
  - apply cfcontext_to_Tmcf_isSupport.
    destruct (cfassign_cf_iter_π₁idP δ H Hδ) as [ge e].
    rewrite e; clear e.
    unfold cf_iter_π₂.
    rewrite Tmscf_nestediterπ₁.
    unshelve econstructor.
    { 
      exact ((n-i) - 1). }
    apply cfassign_iter_π₁.
    assert (e:m = (i + (m - n) + S (n - i - 1))) by lia.
    destruct e.
    constructor.
  - destruct n.
    { exfalso. apply (contextof_snoc_false H). }
    apply cfcontext_to_Tmcf_isSupport.
    unfold cf_iter_π₂.
    unshelve econstructor.
    { exact (n-i). }
    apply cfassign_iter_π₁.
    assert (e : forall q, i + S q = S (i + q)) by lia.
    rewrite e; clear e.
    assert (e : n = i+(n-i)) by lia; destruct e.
    apply cfassign_snoc.
    + exact (assignof_snoc H).
    + exact (contextof_snoc H).
Qed.
Theorem cfassign_to_Tmscf_isSupport (δ:Tmscf) m n
  (H : cfassign m n δ)
  : Tmscf_isSupport m n δ.
Proof.
  destruct (Tmscf_normalization δ) as [δnf [δred δnf_is]].
  rewrite δred.
  apply cfassign_to_Tmscf_isSupport_values.
  - exact (Tmscfσnf_is_value _ δnf_is).
  - exact (cfassign_preserved δred H).
Qed.

End cfassign_to_Tmscf_isSupport.

(* The converse hold only for values:
  For AKcf values, [Tmscf_isSupport] implies [cfassign] *)
Theorem Tmscf_isSupport_to_cfassign_values (δ:Tmscf) {m n}
  (isV : Tmscfσvalue δ)
  (H : Tmscf_isSupport m n δ)
  : cfassign m n δ.
Proof.
  revert m n H; induction isV; intros m n [piδred δisupp].
  - unfold Tmscf_isPreSupport in piδred.
    destruct (cf_iter_π₁idP_to_cf_iter_π₁id Hδ) as [i ?]; subst.
    apply cfassign_iter_π₁.
    assert (e:m = i+n).
    { rewrite Tmscf_nestediterπ₁ in piδred.
      apply cf_iter_π₁id_inj.
      symmetry.
      rewrite Nat.add_comm.
      unshelve eapply (normal_form_rt _ piδred).
      apply Tmcfσnf_cf_iter_π₁id. }
    rewrite e.
    constructor.
  - destruct n.
    { exfalso.
      unfold Tmscf_isPreSupport in piδred; cbn in piδred.
      unshelve eassert (e:=(normal_form_rt _ piδred)).
      { apply Tmscfσvalue_is_nf.
        apply Tmscfσvalue_snoc; assumption. }
      destruct m; discriminate e. }
    constructor.
    + apply IHisV.
      unfold Tmscf_isPreSupport in piδred.
      rewrite cf_iter_π₁_flip in piδred.
      unshelve eassert (e:=(Tmscfσstep_bwtr _ piδred _)).
      3: rewrite cf_π₁beta; reflexivity.
      { apply Tmcfσnf_cf_iter_π₁id. }
      split; [exact e|].
      clear e.
      intros i le.
      unshelve eassert (e:=(δisupp (S i) _)); [lia|].
      unfold cf_iter_π₂ in e.
      rewrite cf_iter_π₁_flip in e.
      rewrite cf_π₁beta in e.
      exact e.
    + apply Tmcf_isSupport_to_cfcontext_values; [assumption|].
      unshelve eassert (e:=(δisupp 0 _)); [lia|].
      unfold cf_iter_π₂ in e; cbn in e.
      rewrite cf_π₂beta in e.
      exact e.
Qed.

(* Corollaries *)
Lemma cfassignm0 {m} (δ : Tmscf) (H:cfassign m 0 δ) : δ <--s>* cf_iter_π₁ m id.
Proof.
  apply clos_rt_clos_rst.
  apply (cfassign_to_Tmscf_isPreSupport _ H).
Qed.

(* "AKcf is finitary" theorem *)
Corollary AKcf_finitary
  : (forall a, exists m, Tmcf_isSupport m a) /\
    forall δ, exists m n, Tmscf_isSupport m n δ.
Proof.
  split.
  - intro a.
    split with (minctx _ (getMinimalContext a)).
    apply cfcontext_to_Tmcf_isSupport.
    apply minctx_ctx.
  - intro δ.
    split with (minass_p _ (getMinimalAssign δ)).
    split with (minass_q _ (getMinimalAssign δ)).
    apply cfassign_to_Tmscf_isSupport.
    apply minass_ass.
Qed.