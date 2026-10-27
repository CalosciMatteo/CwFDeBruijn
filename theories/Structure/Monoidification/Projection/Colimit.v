From Stdlib Require Import Nat PeanoNat Nat Lia EqdepFacts.

From Category Require Import Lib Lib.TList Theory
  Instance.Sets
  Structure.Cone
  Construction.Free.Quiver
  Structure.Limit.
From Category.Functor Require Import Product Hom Opposite.

From CwFdeBruijn Require Import
  CatPsh Uwcwf MwM Contextual
  Lib.Setoid Lib.Transport
  Structure.Uwcwf
  Structure.FlippedComprehension
  Structure.Uwcwf.Transport
  Construction.Monoidification.Projection
  Construction.Monoidification.SubstRel
  Construction.Monoidification.Substitution
  Construction.Monoidification.TmRel
  Structure.FlippedComprehension.IterUpshift
  Structure.FlippedComprehension.IterTmUpshift
  Structure.FlippedComprehension.IterUp
  Construction.Monoidification.CwP

  Instance.FreeOnOneEndo
  Construction.Monoidification.CtxCmp.

Section Colimit.

Context (C:UWCwFN).


(* Diagram D of which Monoidification is the colimit in CwP *)
Section Diagram.

Definition Mndf_D_QuiverHomomorphism
  : QuiverHomomorphism OneEndo_Quiver (QuiverOfCat CwPs).
Proof using C.
  unshelve eapply Build_QuiverHomomorphism.
  - intro.
    simpl.
    apply (UWCwF_incl (UWCwFN_incl C)).
  - intros ? ? ?; cbn.
    apply Up.
  - intros ? ? ? ? E.
    reflexivity.
Defined.

Definition Mndf_D : OneEndo_Category ⟶ CwPs := InducedFunctor OneEndo_Quiver Mndf_D_QuiverHomomorphism.

End Diagram.

Section Diagram_properties.

  Lemma fmap_Mndf_D_1 
    : fmap[Mndf_D^op] OneEndo_arrow ≈ Up.
  Proof.
    cbn -[equiv compose].
    cat.
  Qed.

  Lemma fctx_Mndf_D (Γ:C) (f :  ttt ~{ OneEndo_Category }~> ttt)
    : fctx[ fmap[Mndf_D] f] Γ = iter (tlist_length f) s Γ.
    revert Γ.
    induction f as [|[] [] []]; intros Γ.
    - reflexivity.
    - unshelve etransitivity;
        [exact (fctx[ fmap[Mndf_D] f] (s Γ))|reflexivity |] .
      rewrite IHf, Nat.iter_swap.
      reflexivity.
  Qed.

  Lemma fsbs_Mndf_D (Γ Δ:C) (δ: Γ ~> Δ)
    (f :  ttt ~{ OneEndo_Category }~> ttt)
    (EΓ : iter (tlist_length f) s Γ = fctx[ fmap[Mndf_D] f] Γ)
    (EΔ : iter (tlist_length f) s Δ = fctx[ fmap[Mndf_D] f] Δ)
    : fsbs[ fmap[Mndf_D] f] δ ≈ (iter_upshift_Eq (tlist_length f) EΓ EΔ δ).
  Proof.
    revert Γ Δ δ EΓ EΔ.
    induction f as [|[] [] []]; intros Γ Δ δ EΓ EΔ.
    - now rewrite iter_upshift_Eq_beta_0.
    - unshelve etransitivity.
        { exact (fsbs[ fmap[Mndf_D] f] (↑ δ)). }  {reflexivity. }
      etransitivity. {apply IHf. }
      erewrite <-iter_upshift_Eq_swap.
      reflexivity.
      Unshelve.
      all: symmetry; apply (fctx_Mndf_D).
  Qed.

  Section fsbs_Mndf_D_fixedargs.
    Context (Γ Δ:C) (δ: Γ ~> Δ) (f :  ttt ~{ OneEndo_Category }~> ttt).
    Let EΓ := eq_sym (fctx_Mndf_D Γ f ).
    Let EΔ := eq_sym (fctx_Mndf_D Δ f).

    Lemma fsbs_Mndf_D_fixedargs
      : fsbs[ fmap[Mndf_D] f] δ ≈ (iter_upshift_Eq (tlist_length f) EΓ EΔ δ).
    Proof.
      apply fsbs_Mndf_D.
    Qed.
  End fsbs_Mndf_D_fixedargs.

  Lemma ftm_MndfD {Γ:C} a 
    (f :  ttt ~{ OneEndo_Category }~> ttt)
    (E : iter (tlist_length f) s Γ = fctx[ fmap[Mndf_D] f] Γ)
    : ftm[ fmap[Mndf_D] f] a ≈ iter_Tm_upshift_Eq (tlist_length f) E a.
  Proof.
    revert Γ a E;
      induction f as [|[] [] []]; intros Γ a E.
    - simpl. rewrite iter_Tm_upshift_Eq_beta_0. reflexivity.
    - unshelve etransitivity.
      { exact (ftm[ fmap[Mndf_D] f] (ftm[Up] a)). }  {reflexivity. }
      etransitivity; [apply IHf|].
      erewrite <-(iter_Tm_upshift_Eq_swap (tlist_length f) _ _ a).
      reflexivity.

    Unshelve. symmetry; apply (fctx_Mndf_D).
  Qed.
  Section ftm_MndfD_fixedarg.
    Context {Γ:C} (a : Tm Γ)
      (f :  ttt ~{ OneEndo_Category }~> ttt).

    Let E := eq_sym (fctx_Mndf_D Γ f).

    Lemma ftm_Mndf_D_fixedarg
    : ftm[ fmap[Mndf_D] f] a ≈ iter_Tm_upshift_Eq (tlist_length f) E a.
    Proof. apply ftm_MndfD. Qed.

  End ftm_MndfD_fixedarg.


End Diagram_properties.


(* Mndf is a cocone in CwP*)
Section Mndf_Cocone.
Program Definition Mndf_coconeFrom
  : @ACone _ (Opposite.Opposite CwPs) (Mndf_MwM C) Mndf_D^op := {|
    vertex_map
      := λ x , ((Mndf_U_CwP_Morphism C) :
Mndf_CwP C ~{ Opposite.Opposite CwPs }~> fobj[Mndf_D^op] x)
  |}.
Final Obligation.
  destruct x, y.
  change (ttt ~{OneEndo_Category}~> ttt) in f.
  unshelve eapply make_CwP_Morphism_equiv.
  - reflexivity.
  - intros Γ Δ δ.
    cbn beta; cbn [Logic.transport]; cbn -[Mndf_D equiv]; simpl in Γ, Δ, δ.
    etransitivity; [| eapply Mndf_S_rel_iter_upshift_Eq' ].
    apply make_Mndf_S_rel_samectx. 
    apply fsbs_Mndf_D_fixedargs.
  - intros Γ a.
    cbn [Logic.transport]; cbn -[Mndf_D equiv].
    etransitivity; [|eapply Mndf_T_rel_iter_upshift_Eq'].
    apply make_Mndf_T_rel_samectx.
    apply ftm_Mndf_D_fixedarg.
Qed.

Definition Mndf_Cocone : @Cocone _ CwPs (Mndf_D) :={|
  coneFrom := Mndf_coconeFrom
|}.

Definition Mndf_Cocone_vertex_map
  := ( @vertex_map _ _ _ _ ( @coneFrom _ _ _ Mndf_Cocone) ttt).

End Mndf_Cocone.

(* Lemmas about cocones of D *)
Section Other_Cocones.

Context (FD : Cone (Mndf_D^op)).
Let D := vertex_obj[FD].

Context (ctx_D_UIP : UIP_ (obj[D])).


Definition Mndf_D_vertex_map 
  : C ~{CwPs}~> D
  := ( @vertex_map _ _ _ _ ( @coneFrom _ _ _ FD) ttt).

Definition candidate_distobj : vertex_obj[FD] := fctx[Mndf_D_vertex_map] (⋆_ C).
Definition candidate_substset := candidate_distobj ~{D}~> candidate_distobj.
Definition candidate_termset := Tm candidate_distobj.

Lemma Mndf_D_cone_coherence i
  : Mndf_D_vertex_map ∘ (iter_Up i) ≈ Mndf_D_vertex_map  .
Proof.
  induction i; [cat|].
  assert (H := (@cone_coherence _ _ _ _ (@coneFrom _ _ _ FD) _ _ OneEndo_arrow)).
  rewrite fmap_Mndf_D_1 in H.
  change (iter_Up (S i)) with (Up ∘ @iter_Up C i).
  change (Mndf_D_vertex_map ∘[CwPs] Up ≈ Mndf_D_vertex_map) in H.
  
  rewrite comp_assoc.
  rewrite H.
  apply IHi.
Qed.

Lemma candidate_distobj_uniqueness_nat (i : nat)
  : fctx[Mndf_D_vertex_map] (fctx[iter_Up i] (⋆_ _)) = candidate_distobj.
Proof.
  refine ((`1 `1 (Mndf_D_cone_coherence i)) (⋆_C)).
Defined.

Lemma Mndf_D_cone_coherence_1
  : Mndf_D_vertex_map ≈ Mndf_D_vertex_map ∘ Up.
Proof.
  assert (H := (Mndf_D_cone_coherence 1)).
  cbn -[equiv compose id] in H.
  cat.
Qed.

Lemma candidate_distobj_uniqueness (m : C) : fctx[Mndf_D_vertex_map] m = candidate_distobj.
Proof.
  refine (eq_trans (f_equal (fctx[Mndf_D_vertex_map]) (ctx_to_iter_Up m)) _).
  apply candidate_distobj_uniqueness_nat.
Defined.

Lemma candidate_distobj_uniqueness_desiderata (m:C) (i:nat)
  : candidate_distobj_uniqueness (fctx[ iter_Up i] m) =
eq_trans (projT1 (projT1 (Mndf_D_cone_coherence i)) m)
(candidate_distobj_uniqueness m).
Proof using C D FD ctx_D_UIP.
  apply ctx_D_UIP.
Qed.

Definition cast_to_candidate_substset' {fm fn : D}
  (Em : fm = candidate_distobj) (En : fn = candidate_distobj)
  (δ : fm ~{D}~> fn)
  : candidate_substset
  := homcast Em En δ.
#[global]
Instance proper_cast_to_candidate_substset' {fm fn Em En} : (Proper (equiv ==> equiv) (@cast_to_candidate_substset' fm fn Em En)).
Proof.
  apply proper_homcast.
Qed.

Definition cast_to_candidate_substset {m n: C}
  (δ : fctx[ Mndf_D_vertex_map] m ~{D}~> fctx[ Mndf_D_vertex_map] n)
  : candidate_substset
  := cast_to_candidate_substset' (candidate_distobj_uniqueness m) (candidate_distobj_uniqueness n) δ.
#[global]
Instance proper_cast_to_candidate_substset {m n} : (Proper (equiv ==> equiv) (@cast_to_candidate_substset m n)).
Proof.
  apply proper_homcast.
Qed.

Definition Mndf_D_cone_fsbs {m n : C} (δ : m ~{C}~> n)
  : candidate_substset
  := cast_to_candidate_substset (fsbs[Mndf_D_vertex_map] δ).

Definition Mndf_D_cone_fsbs_rew 
  {m n : C} (δ : m ~{C}~> n)
  {m' n' : C} (δ' : m' ~{C}~> n')
  (Em: m = m') (En: n = n') 
  (Eδ : δ' ≈ homcast Em En δ)
  : Mndf_D_cone_fsbs δ ≈ Mndf_D_cone_fsbs δ'.
Proof.
  destruct Em, En.
  simpl in Eδ.
  unfold Mndf_D_cone_fsbs.
  rewrite Eδ.
  reflexivity.
Qed.

Lemma Mndf_D_cone_coherence_eq_on_sbs 
  {m n : C} {δ : m ~> n} i
  : Mndf_D_cone_fsbs (fsbs[iter_Up i] δ) ≈ Mndf_D_cone_fsbs δ. 
Proof using ctx_D_UIP.
  unfold Mndf_D_cone_fsbs.
  rewrite <-(CwP_Morphism_equiv_eq_on_sbs (Mndf_D_cone_coherence i) δ).
  unfold cast_to_candidate_substset, cast_to_candidate_substset'.
  rewrite homcast_trans.
  apply eq_to_equiv; apply homcast_rew.
  all: apply candidate_distobj_uniqueness_desiderata.
Qed.

Lemma Mndf_D_cone_coherence_eq_on_sbs_iter_upshift
  {m n : C} {δ : m ~> n}
  i {itism itisn}
  (Em : iter i s m = itism) 
  (En : iter i s n = itisn) 
  : Mndf_D_cone_fsbs (iter_upshift_Eq i Em En δ) ≈ Mndf_D_cone_fsbs δ. 
Proof using ctx_D_UIP.
  etransitivity.
  { refine (Mndf_D_cone_fsbs_rew _ (fsbs[iter_Up i] δ) _ _ _  ).
    rewrite fsbs_iter_Up_fixedargs.
    rewrite homcast_iter_upshift_Eq.
    apply iter_upshift_Eq_rew'.
    reflexivity. 
    Unshelve.
    all: rewrite <-?Em, <-?En, fctx_iter_Up; reflexivity. }
  apply Mndf_D_cone_coherence_eq_on_sbs.
Qed.

Definition cast_to_candidate_termset' {fm : D}
  (E : fm = candidate_distobj)
  (a : Tm fm)
  : candidate_termset
  := Logic.transport (fobj[@Tm D]) E a.
#[global]
Instance proper_cast_to_candidate_termset' {fm E} : (Proper (equiv ==> equiv)) (@cast_to_candidate_termset' fm E).
Proof.
  intros ? ? ?.
  unfold cast_to_candidate_termset'.
  refine (proper_transport _ (fobj[Tm]) _ _ _ E _ _ X).
Qed.

Definition cast_to_candidate_termset {m : C}
  (a : Tm (fctx[ Mndf_D_vertex_map] m))
  : candidate_termset
  := cast_to_candidate_termset' (candidate_distobj_uniqueness m) a.
#[global]
Instance proper_cast_to_candidate_termset {m} : (Proper (equiv ==> equiv) (@cast_to_candidate_termset m)).
Proof.
  apply proper_cast_to_candidate_termset'.
Qed.

Definition Mndf_D_cone_ftm {m:C} (a : Tm m) : candidate_termset
  := cast_to_candidate_termset (ftm[Mndf_D_vertex_map] a).

Definition Mndf_D_cone_ftm_rew 
  {m : C} (a : Tm m)
  {m': C} (a' : Tm m')
  (Em: m = m') 
  (Ea : a' ≈ Logic.transport (fobj[Tm]) Em a)
  : Mndf_D_cone_ftm a ≈ Mndf_D_cone_ftm a'.
Proof.
  destruct Em.
  simpl in Ea.
  unfold Mndf_D_cone_ftm.
  rewrite Ea.
  reflexivity.
Qed.


Lemma Mndf_D_cone_coherence_eq_on_tm 
  {m : C} {a : Tm m } i
  : Mndf_D_cone_ftm (ftm[iter_Up i] a) ≈ Mndf_D_cone_ftm a. 
Proof using ctx_D_UIP.
  unfold Mndf_D_cone_ftm.
  rewrite <-(CwP_Morphism_equiv_eq_on_tm (Mndf_D_cone_coherence i) a).
  unfold cast_to_candidate_termset, cast_to_candidate_termset'.
  rewrite transport_trans.
  f_equiv.
  apply candidate_distobj_uniqueness_desiderata.
Qed.

Lemma Mndf_D_cone_coherence_eq_on_tm_iter_Tm_upshift
  {m : C} {a : Tm m}
  i {itism}
  (Em : iter i s m = itism) 
  : Mndf_D_cone_ftm (iter_Tm_upshift_Eq i Em a) ≈ Mndf_D_cone_ftm a. 
Proof using ctx_D_UIP.
  etransitivity.
  { refine (Mndf_D_cone_ftm_rew _ (ftm[iter_Up i] a) _ _ ).
    rewrite ftm_iter_Up_fixedargs.
    rewrite transport_iter_Tm_upshift_Eq.
    apply iter_Tm_upshift_Eq_rew'.
    reflexivity. 
    Unshelve.
      rewrite <-Em; simpl; rewrite fctx_iter_Up; reflexivity. }
  apply Mndf_D_cone_coherence_eq_on_tm.
Qed.

End Other_Cocones.

Arguments candidate_distobj_uniqueness {_} _.

(* Mndf is a colimit *)
Section Universal_Arrow.

Context (FD : Cone (Mndf_D^op))  (ctx_D_UIP : UIP_ (obj[vertex_obj[FD]])).

Program Definition Mndf_D_Colimit_UnivArrow_ctx_fnc
  : Mndf_CwP C ⟶ vertex_obj[FD] := {|
    fobj := λ _, candidate_distobj FD;
    fmap := λ _ _ δ, Mndf_D_cone_fsbs _ (Mndf_S_rep δ);
  |}.
Next Obligation.
  simpl; intros δ γ E; simpl.
  destruct E as [r1 r2 m n Er1m Er1n Er2m Er2n E].

  erewrite <-(Mndf_D_cone_coherence_eq_on_sbs_iter_upshift _ _
    (δ := Mndf_S_rep δ) r1).
  erewrite <-(Mndf_D_cone_coherence_eq_on_sbs_iter_upshift _ _
    (δ := Mndf_S_rep γ) r2).
  
  apply  (Mndf_D_cone_fsbs_rew FD _ _ eq_refl eq_refl).
  simpl.
  symmetry.
  exact E.

  Unshelve.
  all: apply ctx_D_UIP.
Qed.
Next Obligation.
  simpl.
  unfold Mndf_D_cone_fsbs.
  rewrite fmap_id.
  unfold cast_to_candidate_substset, cast_to_candidate_substset'.
  apply eq_to_equiv. apply homcast_id.
Qed.
Obligation Tactic := idtac. Final Obligation. 
  intros ? ? ? δ γ.
  cbn -[homcast].
  etransitivity.
  { unfold Mndf_D_cone_fsbs, cast_to_candidate_substset,
      cast_to_candidate_substset'.
    rewrite fmap_comp.
    erewrite homcast_comp.
    reflexivity. }
  f_equiv.
  + unshelve etransitivity.
    { eapply (Mndf_D_cone_fsbs FD
        (iter_upshift_Eq _ _ eq_refl (Mndf_S_rep δ))). }
    { unfold Mndf_D_cone_fsbs, cast_to_candidate_substset, cast_to_candidate_substset'.
      reflexivity. }
    apply Mndf_D_cone_coherence_eq_on_sbs_iter_upshift.
    apply ctx_D_UIP.
  + unshelve etransitivity.
    { eapply (Mndf_D_cone_fsbs FD
        (iter_upshift_Eq _ eq_refl _ (Mndf_S_rep γ))). }
    { unfold Mndf_D_cone_fsbs, cast_to_candidate_substset, cast_to_candidate_substset'.
      reflexivity. }
    apply Mndf_D_cone_coherence_eq_on_sbs_iter_upshift.
    apply ctx_D_UIP.
Qed. Obligation Tactic := cat_simpl.

Program Definition Mndf_D_Colimit_UnivArrow_tm_ntr : Tm ⟹ Tm ◯ Mndf_D_Colimit_UnivArrow_ctx_fnc^op
:= Build_Transform'
        (λ m , {| morphism := λ a, Mndf_D_cone_ftm _ (Mndf_T_rep a); |}
          : fobj[Tm ] m ~{ Sets }~> fobj[Tm ◯ Mndf_D_Colimit_UnivArrow_ctx_fnc^op] m)
        _ .
Next Obligation.
  destruct m.
  intros a a' E.
  destruct E as [r1 r2 m  Er1 Er2 E].
  rewrite <-(Mndf_D_cone_coherence_eq_on_tm_iter_Tm_upshift 
    _ ctx_D_UIP (a:= Mndf_T_rep a)).
  rewrite <-(Mndf_D_cone_coherence_eq_on_tm_iter_Tm_upshift 
    _ ctx_D_UIP (a:= Mndf_T_rep a')).
  apply (Mndf_D_cone_ftm_rew FD _ _ eq_refl).
  simpl.
  symmetry.
  exact E.
Qed.
Obligation Tactic := idtac. Final Obligation. 
  intros [] [] δ a.
  simpl in δ, a.
  cbn -[Mndf_D_cone_ftm Mndf_D_cone_fsbs iter_upshift_Eq Mndf_T_subst].
  symmetry.
  
  etransitivity.
  { unfold Mndf_D_cone_ftm, cast_to_candidate_termset,
      cast_to_candidate_termset'.
      refine (proper_transport _ (fobj[Tm]) _ _ _ (candidate_distobj_uniqueness _) _ _ _).

      refine (morph_subst (Mndf_D_vertex_map FD) _ _). }
  erewrite transport_subst.
  change (fmap[Tm]
    (Mndf_D_cone_fsbs FD (Mndf_S_rep δ))
    (Mndf_D_cone_ftm FD (Mndf_T_rep a)))
  with
    ((Mndf_D_cone_ftm FD (Mndf_T_rep a)) 
    [(Mndf_D_cone_fsbs FD (Mndf_S_rep δ))]).
  f_equiv.
  + unshelve etransitivity.
    { eapply (Mndf_D_cone_ftm FD
        (iter_Tm_upshift_Eq _ _ (Mndf_T_rep a))). }
    { unfold Mndf_D_cone_ftm, cast_to_candidate_termset, cast_to_candidate_termset'.
      reflexivity. }
    apply Mndf_D_cone_coherence_eq_on_tm_iter_Tm_upshift.
    apply ctx_D_UIP.
  + unshelve etransitivity.
    { eapply (Mndf_D_cone_fsbs FD
        (iter_upshift_Eq _ eq_refl _ (Mndf_S_rep δ))). }
    { unfold Mndf_D_cone_fsbs, cast_to_candidate_substset, cast_to_candidate_substset', Mndf_T_subst, Mndf_T_subst'.
      cbn [Mndf_T_m].
      reflexivity. }
    apply Mndf_D_cone_coherence_eq_on_sbs_iter_upshift.
    apply ctx_D_UIP.
Qed. Obligation Tactic := cat_simpl.

Definition Mndf_D_Colimit_UnivArrow
  : CwP_Morphism (Mndf_CwP C) vertex_obj[FD] :={|
    ctx_fnc := Mndf_D_Colimit_UnivArrow_ctx_fnc;
    tm_ntr := Mndf_D_Colimit_UnivArrow_tm_ntr
  |}.

Lemma Mndf_D_Colimit_UnivArrow_commutes
  : Mndf_Cocone_vertex_map ∘ Mndf_D_Colimit_UnivArrow
    ≈ vertex_map[FD].
Proof.
  unshelve eapply make_CwP_Morphism_equiv.
  - intros Γ.
    symmetry.
    apply candidate_distobj_uniqueness.
  - intros Γ Δ δ.
    cbn beta.
    simpl.
    unfold Mndf_D_cone_fsbs.
    unfold cast_to_candidate_substset, cast_to_candidate_substset'.
    rewrite homcast_trans.
    rewrite !eq_trans_sym_inv_r.
    reflexivity.
  - intros Γ a.
    simpl.
    unfold Mndf_D_cone_ftm,
      cast_to_candidate_termset, cast_to_candidate_termset'.
    rewrite transport_trans.
    rewrite eq_trans_sym_inv_r.
    reflexivity.
Qed.

End Universal_Arrow.

Section Colimit.

Context (ctx_D_UIP : forall (FD : Cone (Mndf_D^op)), UIP_ (obj[vertex_obj[FD]])).

Definition Mndf_D_Colimit : Colimit (Mndf_D).
Proof using ctx_D_UIP.
  eapply (Build_Limit _ _ _ Mndf_Cocone).
  intros FD; unshelve esplit.
  - apply Mndf_D_Colimit_UnivArrow.
    apply ctx_D_UIP.
  - intros [].
    apply Mndf_D_Colimit_UnivArrow_commutes.
  - intros V H.
    change (vertex_obj[Mndf_Cocone] ~{CwPs}~>  vertex_obj[FD]) in V.
    specialize (H ttt).
    change (V ∘ (Mndf_U_CwP_Morphism C ) ≈ (( @vertex_map _ _ _ _ ( @coneFrom _ _ _ FD) ttt))) in H.

    unshelve eapply Mndf_U_CwP_Morphism_epic.
    2:{ intro. apply ctx_D_UIP. }
    etransitivity.
    2: symmetry; apply H.
    apply Mndf_D_Colimit_UnivArrow_commutes.
Qed.
End Colimit.

(* [Mndf_D_Colimit_UnivArrow] is a UWCWF morphism
  if D is a MwM and F is  wCwF-morphism *)
Section Colimit_UnivArrow_wCwF_morphism.
  Context (FD : Cone (Mndf_D^op)).
  Context 
    (is_UWCwF : @UnitypedWeakCwF vertex_obj[FD])
    (is_MwM : @MonoidWithModule (vertex_obj[FD];is_UWCwF)).
  Let D := ((vertex_obj[FD];is_UWCwF);is_MwM) : MwM.
  Let UIP : UIP_ obj[vertex_obj[FD]] := (contraction_to_UIP _ (@MwM_contraction D)).

  Context (is_UWCwF_Morphism : @UWCwF_Morphism (C:UWCwF) (D:UWCwF)
   (Mndf_D_vertex_map FD : C ~{ CwPs }~> D)).
  
  Lemma Mndf_D_Colimit_UnivArrow_UWCwF_Morphism
    : @UWCwF_Morphism (Mndf_MwM C) D (Mndf_D_Colimit_UnivArrow FD UIP).
  Proof using is_UWCwF_Morphism.
    unshelve eapply make_uwcwfmorphism.
    - intros x.
      apply MwM_prop.
    - apply hasSingleContext.
      exact is_MwM.
    - intros [] [] δ.
      simpl in δ; simpl.

      unfold Mndf_D_cone_fsbs, cast_to_candidate_substset,
      cast_to_candidate_substset'.
      rewrite (pi1_preserved _ is_UWCwF_Morphism _ _ (↑(Mndf_S_rep δ))).
      etransitivity.
      { apply eq_to_equiv.
        refine (@homcast_π1 D
          (fctx[ Mndf_D_vertex_map FD] (s (Mndf_S_m δ)))
          _
          (fctx[ Mndf_D_vertex_map FD] (Mndf_S_n δ))
          _
          (candidate_distobj_uniqueness (s (Mndf_S_m δ)))
          (candidate_distobj_uniqueness (Mndf_S_n δ))
          _
          ). }
      change (↑(Mndf_S_rep δ)) with (fsbs[Up] (Mndf_S_rep δ)).
      rewrite <- (CwP_Morphism_equiv_eq_on_sbs (Mndf_D_cone_coherence_1 FD) (Mndf_S_rep δ)).
      f_equiv.
      rewrite homcast_transport_cod, transport_homcast_cod, homcast_trans.
      erewrite homcast_rew.
      { reflexivity. }
      all: apply UIP.
    - intros [] [] δ.
      simpl in δ; simpl.
      unfold Mndf_D_cone_ftm, cast_to_candidate_termset,
      cast_to_candidate_termset'.
      rewrite (pi2_preserved _ is_UWCwF_Morphism _ _ (↑(Mndf_S_rep δ))).
      etransitivity.
      { simpl.
        apply eq_to_equiv.
        symmetry.
        refine (@pi2_transport_m D _ _ _ _ (candidate_distobj_uniqueness (s (Mndf_S_m δ)))). }
      change (↑(Mndf_S_rep δ)) with (fsbs[Up] (Mndf_S_rep δ)).
      rewrite <- (CwP_Morphism_equiv_eq_on_sbs (Mndf_D_cone_coherence_1 FD) (Mndf_S_rep δ)).

      rewrite transport_homcast_cod, transport_homcast_dom.

      unfold Mndf_D_cone_fsbs, cast_to_candidate_substset,
      cast_to_candidate_substset'.

      apply eq_to_equiv.
      rewrite transport_homcast_cod.
      unshelve refine (@pi2_homcast_2path D _ _ _ _ _ _ _ _ _ _ _ _
        (fsbs[ Mndf_D_vertex_map FD] (Mndf_S_rep δ))).
      
      { apply candidate_distobj_uniqueness. }
      + apply UIP.
      + apply UIP.
  Qed.
  
End Colimit_UnivArrow_wCwF_morphism.

End Colimit.
