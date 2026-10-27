Require Import Equations.Prop.Logic.

Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

From CwFdeBruijn Require Import
  Lib.Transport.

Declare Scope CwF_scope.
Delimit Scope CwF_scope with CwF.
Open Scope CwF_scope.

Record CwP : Type := make_cwp {
  ctx :> Category;
  Tm : [(ctx ^op), Sets];
}.
Arguments Tm {_}.

Record CwP_Morphism (C D : CwP) := make_cwpmorphism {
  ctx_fnc : ctx C ⟶ ctx D;
  tm_ntr : (@Tm C) ⟹ (@Tm D) ◯ (ctx_fnc^op);
}.
Notation "fctx[ F ]" := (fobj[@ctx_fnc _ _ F]) (at level 9): CwF_scope.
Notation "fsbs[ F ]" := (fmap[@ctx_fnc _ _ F]) (at level 9): CwF_scope.
Notation "ftm[ F ]" := (transform[@tm_ntr _ _ F] _) (at level 9): CwF_scope.

Arguments ctx_fnc {_ _} _.
Arguments tm_ntr {_ _} _.

Lemma transport_naturaility (C: Category) (F G : @Functor C Sets) (A : F ⟹ G) 
  (c c' : C) (p : c = c') (a : fobj[F] c)
  : transform[A] c' (transport (fun z => fobj[F] z) p a) ≈
      transport (fun z => (fobj[G] z)) p (transform[A] c a).
Proof.
  destruct p. reflexivity.
Qed.

Definition subst {C : CwP} {m n : C} (a: Tm n) (δ : m ~{C}~> n)
  : Tm m
  := fmap[Tm] δ a.
#[global]
Instance proper_subst {C : CwP} {m n:C} : (Proper (equiv ==> equiv ==> equiv) (@subst _ m n)).
Proof.
  intros ? ? E1 ? ? E2.
  unfold subst.
  rewrite E1.
  generalize y.
  apply (fmap_respects (Functor := Tm) _ _ _ _ E2).
Qed.
Notation "a '[' δ ']'" := (subst a δ).

Section CwP_DefProperties.
Context {C : CwP}.

(* Functoriality of `Tm` gives *)
Lemma substsubst {m' m n : C} (a: Tm n) (δ : m ~{C}~> n) (γ : m' ~> m)
  : a[δ][γ] ≈ a[δ ∘ γ].
Proof.
  symmetry.
  apply ((fmap_comp (Functor:= Tm)) γ δ a).
Qed.

Lemma substid {n : C} (a: Tm n)
  : a[id] ≈ a.
Proof.
  exact (fmap_id (Functor:= Tm) a).
Qed.

End CwP_DefProperties.

Section CwPMorphism_DefProperties.

Context {C D : CwP} (F : CwP_Morphism C D).

(* Naturality of `tm_ntr` gives *)
Lemma morph_subst' {m n : C} (δ : m~>n) (a : fobj[Tm] n)
  : ftm[ F ] (fmap[Tm] δ a) ≈ fmap[Tm] (fsbs[ F ] δ) (ftm[F] a).
Proof.
  symmetry.
  apply (naturality[tm_ntr F] _ _ δ a).
Qed.  
Lemma morph_subst {m n : C} (δ : m~>n) (a : fobj[Tm] n)
  : ftm[F] (a[δ]) ≈ (ftm[F] a)[fsbs[F] δ].
Proof.
  apply morph_subst'.
Qed.
Lemma ftm_subst {m n : C} (δ : m~>n) (a : fobj[Tm] n)
  : ftm[F] (a[δ]) ≈ (ftm[F] a)[fsbs[F] δ].
Proof.
  apply morph_subst.
Qed. 

End CwPMorphism_DefProperties.


Definition CwP_Morphism_equiv {C D : CwP} : crelation (CwP_Morphism C D)
  := fun (F G : CwP_Morphism C D) =>
    { ctx_fnc_equiv
        : @equiv _ Functor_StrictEq_Setoid (ctx_fnc F) (ctx_fnc G)
          & forall (Γ : C) (a : Tm Γ),
            transport (fobj[@Tm D]) (`1 ctx_fnc_equiv Γ) (ftm[F] a) ≈ ftm[G] a }.

Lemma Functor_StrictEq_eq_on_sbs {C D : Category} {F G : C ⟶ D}
  (E : @equiv _ Functor_StrictEq_Setoid F G) 
  (Γ Δ : C) (δ : Γ ~> Δ)
  : homcast (`1 E Γ) (`1 E Δ) (fmap[F] δ)
      ≈ fmap[G] δ.
Proof.
  refine (fst (transport_adjunction obj[D]
      (λ x, x ~{ D }~> fobj[ G] Δ)
      (λ x, equiv) _ _ (_) _ _ ) _).
  apply `2 E.
Qed.

Definition make_CwP_Morphism_equiv {C D : CwP} {F G : CwP_Morphism C D}
  (eq_on_obj : ∀ Γ : C, fctx[F] Γ = fctx[G] Γ)
  (eq_on_sbs : ∀ (Γ Δ : C) (δ : Γ ~> Δ),
      homcast (eq_on_obj Γ) (eq_on_obj Δ) (fsbs[F] δ)
      ≈ fsbs[G] δ)
  (eq_on_tm : ∀ (Γ : C) (a : Tm Γ),
    transport (fobj[@Tm D]) (eq_on_obj Γ) (ftm[F] a) ≈ ftm[G] a)
  : CwP_Morphism_equiv F G.
Proof.
  unshelve esplit; [esplit with eq_on_obj|].
  - intros Γ Δ δ.
    refine (snd (transport_adjunction obj[D]
      (λ x, x ~{ D }~> fctx[ G] Δ)
      (λ x, equiv) _ _ (_) _ _ ) _).
    apply eq_on_sbs.
  - apply eq_on_tm.
Defined.

Lemma CwP_Morphism_equiv_destruct {C D : CwP} {F G : CwP_Morphism C D} 
  (P : Type)
  (H : forall (eq_on_obj : ∀ Γ : C, fctx[F] Γ = fctx[G] Γ)
      (eq_on_sbs : ∀ (Γ Δ : C) (δ : Γ ~> Δ),
        homcast (eq_on_obj Γ) (eq_on_obj Δ) (fsbs[F] δ)
          ≈ fsbs[G] δ)
      (eq_on_tm : ∀ (Γ : C) (a : Tm Γ),
        transport (fobj[@Tm D]) (eq_on_obj Γ) (ftm[F] a) ≈ ftm[G] a),     
    P )
  (E : CwP_Morphism_equiv F G ) : P.
Proof.
  destruct E as [E_fnc E_tm].
  assert (E_sbs := (Functor_StrictEq_eq_on_sbs E_fnc)).
  destruct E_fnc as [E_ctx e].
  simpl in *.
  clear e.
  exact (H E_ctx E_sbs E_tm).
Defined.

Program Instance CwP_Morphism_Setoid {C D : CwP} :
  Setoid (CwP_Morphism C D) := {|
  equiv := CwP_Morphism_equiv;
|}.
Final Obligation.
  apply Build_Equivalence.
  - intro F.
    unshelve eapply make_CwP_Morphism_equiv.
    + exact (λ _, eq_refl).
    + reflexivity.
    + reflexivity.
  - intros F G.
    destruct 1 as [E_ctx E_sbs E_tm] using CwP_Morphism_equiv_destruct.

    unshelve eapply make_CwP_Morphism_equiv.
    + intros Γ. 
      symmetry; apply E_ctx.
    + intros Γ Δ δ.
      specialize (E_sbs Γ Δ δ).
      simpl.
      refine (symmetry (snd (transport_adjunction obj[D]
        (λ x, x ~{ D }~> fctx[ F] Δ)
        (λ x, equiv) _ _ (E_ctx Γ) _ _ ) _)).

      refine (snd (transport_adjunction obj[D]
        (λ x,  fctx[ G] Γ ~{ D }~> x)
        (λ x, equiv) _ _ (E_ctx Δ) _ _ ) _).

      rewrite transport_domcod_to_coddom.
      exact E_sbs.
    + intros Γ a.
      simpl; simpl in E_tm.
      specialize (E_tm Γ a).
      refine (fst (transport_adjunction obj[D] (λ x, fobj[Tm] x) (λ x, equiv)
        _ _ (Compat.eq_sym (E_ctx Γ)) _ _ ) _).
      unfold transport_r.
      rewrite eq_sym_involutive.
      symmetry.
      exact E_tm.
  - intros F G H.
  destruct 1 as [EFG_ctx EFG_sbs EFG_tm] using CwP_Morphism_equiv_destruct.
  destruct 1 as [EGH_ctx EGH_sbs EGH_tm] using CwP_Morphism_equiv_destruct.
  simpl in *.
  unshelve eapply make_CwP_Morphism_equiv.
  + intros Γ.
    exact (eq_trans (EFG_ctx Γ) (EGH_ctx Γ)).
  + intros Γ Δ δ.
    simpl.
    rewrite <-!homcast_trans.
    rewrite (EFG_sbs Γ Δ δ).
    rewrite (EGH_sbs _ _ δ).
    reflexivity.
  + intros Γ a.
    simpl.
    etransitivity; [|apply EGH_tm].
    rewrite <-transport_trans.
    refine (proper_transport _ (fobj[Tm]) _ _ _ (EGH_ctx Γ) _ _ _).
    apply EFG_tm.
Qed.

Definition CwP_Morphism_id_tmntr (C : CwP)
  : Tm ⟹ Tm ◯ (Id[C])^op.
Proof.
  unshelve eapply Build_Transform'.
  - cat_simpl.
    apply (id{Sets}).
  - cat_simpl.
Defined.

Definition CwP_Morphism_id {C : CwP} :
  CwP_Morphism C C := {|
  ctx_fnc := Id[C];
  tm_ntr  := CwP_Morphism_id_tmntr C;
|}.

Program Definition CwP_Morphism_compose_tmntr {B C D : CwP}
  (G : CwP_Morphism C D)
  (F : CwP_Morphism B C)
  : Tm ⟹ Tm ◯ (ctx_fnc G ◯ ctx_fnc F)^op
  := Build_Transform'
    (λ n, ({|
      morphism := (tm_ntr G (ctx_fnc F n)) ∘ (tm_ntr F n)
      |})
      : (fobj[Tm] n) ~{Sets}~> (fobj[Tm ◯ ((ctx_fnc G) ◯ (ctx_fnc F))^op] n))
    _.
Final Obligation.
  rewrite morph_subst'.
  rewrite morph_subst'.
  reflexivity.
Qed.

Program Definition CwP_Morphism_compose {B C D : CwP}
  (G : CwP_Morphism C D)
  (F : CwP_Morphism B C) :
  CwP_Morphism B D := {|
  ctx_fnc := (ctx_fnc G) ◯ (ctx_fnc F);
  tm_ntr  := CwP_Morphism_compose_tmntr G F ;
|}.

Program Definition CwPs : Category := {|
  obj     := CwP;
  hom     := λ F G, CwP_Morphism F G;
  homset  := λ F G, @CwP_Morphism_Setoid F G;
  id      := λ C, @CwP_Morphism_id C;
  compose := λ F G H, @CwP_Morphism_compose F G H;
|}.
Next Obligation.
intros  F F'.
destruct 1 as [EF_ctx EF_sbs EF_tm] using CwP_Morphism_equiv_destruct.
intros  G G'.
destruct 1 as [EG_ctx EG_sbs EG_tm] using CwP_Morphism_equiv_destruct.
unshelve eapply make_CwP_Morphism_equiv.
- intro Γ; simpl.
  exact (eq_trans (EF_ctx (fctx[ G] Γ)) (f_equal (fctx[ F']) (EG_ctx Γ))).
- intros Γ Δ δ; simpl in *.
  rewrite <-!homcast_trans.
  rewrite (EF_sbs _ _ (fsbs[ G] δ)).
  unfold homcast.
  rewrite <-transport_functorial_cod, <-transport_functorial_dom.
  f_equiv.
  apply EG_sbs.
- intros Γ a; simpl in *.
  rewrite <-!transport_trans.
  etransitivity.
  { refine (proper_transport _ _ _ _ _ _ _ _ _).
    apply EF_tm. }
  rewrite <-transport_f_equal.

  change  (λ a0 : obj[y], fobj[Tm] (fctx[ F'] a0)) with (λ z0 : obj[y^op], fobj[Tm ◯ (ctx_fnc F')^op] z0).
  rewrite <-(transport_naturaility _ _  _ (tm_ntr F')).
  apply (proper_morphism (ftm[ _])).
  apply EG_tm.
Qed.
Next Obligation. unshelve eapply make_CwP_Morphism_equiv; reflexivity. Qed.
Next Obligation. unshelve eapply make_CwP_Morphism_equiv; reflexivity. Qed.
Next Obligation. unshelve eapply make_CwP_Morphism_equiv; reflexivity. Qed.
Final Obligation. unshelve eapply make_CwP_Morphism_equiv; reflexivity. Qed.

Section CwPMorphism_Properties.
  Lemma fsbs_comp_eq {C D E: CwP}
    (F : CwP_Morphism D E) (G : CwP_Morphism C D)
    {c' c : C} (δ : c'~>c)
  : fsbs[F ∘[CwPs] G] δ =
    fsbs[F] (fsbs[G] δ).
  Proof.
    reflexivity.
  Defined.

  Lemma fsbs_comp {C D E: CwP}
    (F : CwP_Morphism D E) (G : CwP_Morphism C D)
    {c' c : C} (δ : c'~>c)
  : fsbs[F ∘[CwPs] G] δ ≈
    fsbs[F] (fsbs[G] δ).
  Proof.
    reflexivity.
  Defined.

  Lemma CwP_Morphism_equiv_eq_on_sbs {C D : CwPs} {F G : CwP_Morphism C D} (E : CwP_Morphism_equiv F G)
  {Γ Δ : C} (δ : Γ ~> Δ)
  : homcast (`1 `1 E Γ) (`1 `1 E Δ) (fsbs[F] δ)
      ≈ fsbs[G] δ.
  Proof.
    apply Functor_StrictEq_eq_on_sbs.
  Qed.

  Lemma CwP_Morphism_equiv_eq_on_tm {C D : CwPs} {F G : CwP_Morphism C D} (E : CwP_Morphism_equiv F G)
  {Γ : C} (δ : Tm Γ)
  : transport (fobj[Tm]) (`1 `1 E Γ) (ftm[F] δ)
      ≈ ftm[G] δ.
  Proof.
    apply `2 E.
  Qed.
End CwPMorphism_Properties.

Section transport.
  Lemma transport_subst {C : CwP} {c c' d d' : C}
  (p_c: c = c')
  (p_d: d = d')
  (δ: c ~> d) (a : Tm d)
  : transport (fobj[Tm]) p_c (a[δ]) = (transport (fobj[Tm]) p_d (a))[(homcast p_c p_d δ)].
  Proof.
    destruct p_c, p_d.
    reflexivity.
  Qed.
End transport.