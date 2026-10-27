From Stdlib Require Import Nat PeanoNat.
From Category Require Import Lib Theory.
From Category.Theory Require Import Morphisms.
From Category.Instance Require Import
  Sets Sets.Cartesian
  Fun Fun.Cartesian.
From Category.Construction Require Import Opposite.
From Category.Functor Require Import Product Hom.

From CwFdeBruijn Require Import
  CatPsh
  Uwcwf
  Structure.Uwcwf Structure.Uwcwf.Iter
  Contextual FullSubCategory
  Lib.Transport.

Section FlippedComprehension_def.
  Context (C:UWCwFN).

  Open Scope type_scope.

  Section cons_data_definition.
    Definition cons_data_nat {m : C} {n:nat} : Tm m * (m ~> (ctl_c n)) -> m ~> ctl_c (S n).
    Proof.
      intros [a δ].
      induction n.
      - exact ⟨δ,a⟩.
      - refine ⟨IHn (π1 δ), π2 δ⟩.
    Defined.

    Lemma cons_nat_beta_0 {m : C}
    (a : Tm m) (δ : m ~> (ctl_c 0))
    : cons_data_nat (a,δ) ≈ ⟨ δ , a ⟩.
  Proof.
    reflexivity.
  Qed.

  Lemma cons_nat_beta_S {m : C} {n:nat}
    (a : Tm m) (δ : m ~> (ctl_c (S n)))
    : cons_data_nat (a,δ) = ⟨ cons_data_nat (a,(π1 δ)), π2 δ ⟩.
  Proof.
    reflexivity.
  Qed.

  #[global]
  Instance proper_cons_data_nat {m: C} {n:nat} : (Proper (equiv ==> equiv) (@cons_data_nat m n)).
  Proof.
    induction n.
    - intros [? ?] [? ?] [ETm ESub].
      simpl.
      simpl in ETm, ESub.
      now rewrite ETm, ESub.
    - intros [a δ] [b γ] [ETm ESub].
      simpl in ETm, ESub.
      rewrite !cons_nat_beta_S. (* judgmental *)
      now rewrite ETm, ESub. (* this uses IHn *)
  Qed.

  Definition cons_data {m n : C} : Tm m * (m ~> n) -> m ~> s n.
  Proof.
    intros aδ.
    apply (Logic.transport (λ x,  m ~> x) (f_equal s (nnp_cl _))).
    apply cons_data_nat.
    refine (Logic.transport (λ x,  fobj[Tm] m * (m ~> x)) _ aδ).
    symmetry.
    exact (nnp_cl n).
  Defined.

  #[global]
  Instance proper_cons_data {m n: C} : (Proper (equiv ==> equiv) (@cons_data m n)).
  Proof.
    intros aδ bγ E.
    unfold cons_data.
    apply proper_transport.
    apply proper_cons_data_nat.
    refine (proper_transport _
      (λ x : C, fobj[Tm] m * (m ~> x))
      _
      _ 
      _
      (Compat.eq_sym (nnp_cl n))
      (aδ) (bγ) _ ).
    exact E.
  Qed.

  Lemma cons_nat_to_cons {m : C} {n:nat}
    (aδ : Tm m * (m ~> (ctl_c n)))
    : cons_data_nat aδ = cons_data aδ .
  Proof.
    unfold cons_data.
    rewrite <-(nnp_higher_clc n).
    rewrite eq_sym_map_distr.
    rewrite <-!transport_f_equal.
    rewrite <-(transport_funfam (@cons_data_nat m) _).
    rewrite transport_trans, eq_trans_sym_inv_l.
    reflexivity.
  Qed.

  Lemma cons_data_beta_0
    {m : C} (a : Tm m) (δ : m ~>  (@ctl_c C 0))
    : cons_data (a, δ) = ⟨δ,a⟩.
  Proof.
    rewrite <-cons_nat_to_cons.
    reflexivity.
  Qed.

  Lemma cons_data_beta_distobj
    {m : C} (a : Tm m) (δ : m ~>  (⋆__))
    : cons_data (a, δ) = ⟨δ,a⟩.
  Proof.
    revert δ; rewrite <-(ctl_c_0).
    apply cons_data_beta_0.
  Qed.

  Lemma cons_data_beta_S
    {m : C} (a : Tm m) {n:nat} (δ : m ~>  (@ctl_c C (S n)))
    : cons_data (a, δ) = ⟨cons_data(a, π1 δ), π2 δ⟩.
  Proof.
    rewrite <-cons_nat_to_cons.
    rewrite cons_nat_beta_S.
    rewrite cons_nat_to_cons.
    reflexivity.
  Qed.

  Lemma cons_data_beta_s {m n: C} (a : Tm m) (δ : m ~>  s n)
    : cons_data (a, δ) = ⟨cons_data(a, π1 δ), π2 δ⟩.
  Proof.
    revert δ; rewrite <-(nnp_cl n); intros δ.
    apply cons_data_beta_S.
  Qed.

  End cons_data_definition.

  Section e1_data_definition.


    Definition e1_data_nat {m : C} {n:nat} (δ : m ~> ctl_c (S n)) : Tm m.
    Proof.
      induction n.
      - exact (π2 δ).
      - exact (IHn (π1 δ)).
    Defined.
    #[global]
    Instance proper_e1_data_nat {m: C} {n:nat} : (Proper (equiv ==> equiv) (@e1_data_nat m n)).
    Proof.
      induction n.
      - intros δ γ E.
        rewrite E.
        proper.
      - intros δ γ E.
        simpl.
        refine (IHn (π1 δ) (π1 γ) _).
        rewrite E.
        proper.
    Qed.


    Lemma e1_data_nat_beta_0 {m : C} (δ : m ~> (ctl_c (S 0)))
    : e1_data_nat δ = π2 δ.
    Proof.
      reflexivity.
    Qed.

    Lemma e1_data_nat_beta_S {m : C} {n:nat} (δ : m ~> (ctl_c (S(S n))))
      : e1_data_nat δ = e1_data_nat (π1 δ).
    Proof.
      reflexivity.
    Qed.

    Definition e1_data {m n : C} (δ : m ~> s n)
      : Tm m
      := e1_data_nat
        (Logic.transport_r (λ x, m ~> s x) (nnp_cl n)
        δ).

    #[global]
    Instance proper_e1_data {m n: C} : (Proper (equiv ==> equiv) (@e1_data m n)).
    Proof.
      intros ? ? E.
      unfold e1_data, Logic.transport_r.
      apply proper_e1_data_nat.
      refine (proper_transport
        C
        (λ x, m ~> s x)
        _ _ _ _ _ _ _ ).
      exact E.
    Qed.

    Lemma e1_nat_to_e1 {m : C} {n:nat}
      (δ : m ~> s (ctl_c n))
      : e1_data_nat δ = e1_data δ.
    Proof.
      change (m~>s (ctl_c n)) in δ.
      unfold e1_data. 
      rewrite <-nnp_higher_clc.
      unfold Logic.transport_r.
      rewrite eq_sym_map_distr.
      rewrite <-transport_f_equal.
      rewrite <-(transport_funfam (@e1_data_nat m)).
      destruct (nnp_lc n).
      reflexivity.
    Qed.

    Lemma e1_data_beta_distobj {m : C} (δ : m ~> s (⋆__))
    : e1_data δ = π2 δ.
    Proof.
      revert δ; rewrite <-(ctl_c_0 ); intro δ.
      eapply eq_trans.
      { symmetry. apply e1_nat_to_e1. }
      exact (e1_data_nat_beta_0 δ).
    Qed.
    
    Lemma e1_data_beta_S {m : C} {n:nat} (δ : m ~> s ((@ctl_c C (S n))))
      : e1_data δ = e1_data (π1 δ).
    Proof.
      now rewrite <-!e1_nat_to_e1.
    Qed.

    Lemma e1_data_beta_s {m n : C} (δ : m ~> s (s (n)))
      : e1_data δ = e1_data (π1 δ).
    Proof.
      revert δ; rewrite <-(nnp_cl n); intro δ.
      apply e1_data_beta_S.
    Qed.

  End e1_data_definition.

  Section e2_data_definition.

    Definition e2_data_nat {m : C } {n:nat} (δ : m ~> (ctl_c (S n)))
      : m ~> ctl_c n.
    Proof.
      induction n.
      - exact (π1 δ).
      - refine ⟨IHn (π1 δ),π2 δ⟩.
    Defined.

    #[global]
    Instance proper_e2_data_nat {m: C} {n:nat} : (Proper (equiv ==> equiv) (@e2_data_nat m n)).
    Proof.
      induction n.
      - intros δ γ E.
        simpl.
        rewrite E.
        proper.
      - intros δ γ E.
        simpl.
        unshelve erewrite (IHn (π1 δ) (π1 γ));
          rewrite E; proper.
    Qed.

    Lemma e2_data_nat_beta_0 {m : C} (δ : m ~> (ctl_c (S 0)))
    : e2_data_nat δ = π1 δ.
    Proof.
      reflexivity.
    Qed.

    Lemma e2_data_nat_beta_S {m : C} {n:nat} (δ : m ~> (ctl_c (S(S n))))
      : e2_data_nat δ = ⟨e2_data_nat (π1 δ),π2 δ⟩.
    Proof.
      reflexivity.
    Qed.

    Definition e2_data {m n : C} (δ : m ~> s n) : m ~> n :=
      Logic.transport (λ x,  m ~> x) (nnp_cl n)
        (e2_data_nat
          (Logic.transport _ (f_equal s (eq_sym (nnp_cl n))) δ)).

    #[global]
    Instance proper_e2_data {m n: C} : (Proper (equiv ==> equiv) (@e2_data m n)).
    Proof.
      intros δ γ E.
      unfold e2_data.
      rewrite E.
      proper.
    Qed.

    Lemma e2_nat_to_e2 {m : C} {n:nat}
      (δ : m ~> s (ctl_c n))
      : e2_data_nat δ = e2_data δ.
    Proof.
      change (m~>s (ctl_c n)) in δ.
      unfold e2_data. 
      rewrite <-(nnp_higher_clc n).
      rewrite eq_sym_map_distr.
      rewrite <-!transport_f_equal.
      rewrite <-(transport_funfam (@e2_data_nat m) _).
      rewrite transport_trans, eq_trans_sym_inv_l.
      reflexivity.
    Qed.

    Lemma e2_data_beta_distobj {m : C} (δ : m ~> s (⋆__))
    : e2_data δ = π1 δ.
    Proof.
      revert δ; rewrite <-(ctl_c_0 ); intro δ.
      eapply eq_trans.
      { symmetry. apply e2_nat_to_e2. }
      exact (e2_data_nat_beta_0 δ).
    Qed.
    
    Lemma e2_data_beta_S {m : C} {n:nat} (δ : m ~> s ((@ctl_c C (S n))))
      : e2_data δ = ⟨e2_data (π1 δ),π2 δ⟩.
    Proof.
      now rewrite <-!e2_nat_to_e2.
    Qed.

    Lemma e2_data_beta_s {m n : C} (δ : m ~> s (s (n)))
      : e2_data δ = ⟨e2_data (π1 δ),π2 δ⟩.
    Proof.
      revert δ; rewrite <-(nnp_cl n); intro δ.
      apply e2_data_beta_S.
    Qed.  

  End e2_data_definition.

  Section flpctxcomp_naturality.

    Context {n : C}.

    Program Definition cons'
      : Tm × [Hom ─ , n ] ⟹ [Hom ─ , s n ]
      := Build_Transform'
        (λ m , {| morphism := cons_data; |}
          : fobj[(Tm : obj[[C^op, Sets]]) × [Hom ─ , n ]] m ~{ Sets }~> fobj[[Hom ─ , s n ]] m)
        _.
    Final Obligation.
      induction n using UWCwFN_ind.
      + now rewrite !cons_data_beta_distobj, snoc_comp.
      + now rewrite !cons_data_beta_s, snoc_comp, (IHo (π1 _)), pi1_comp, pi2_subst.
    Qed.

    Program Definition e1' : [Hom ─ , s n ] ~> Tm
      := Build_Transform'
        (λ m,  {|morphism := e1_data|}
          : fobj[[Hom ─ , s n ]] m  ~{ Sets }~> fobj[Tm] m) 
        _.
    Final Obligation.
      induction n using UWCwFN_ind.
      + now rewrite !e1_data_beta_distobj, <-pi2_subst.
      + rewrite !e1_data_beta_s, <-pi1_comp. 
        exact (IHo (π1 _)).
    Qed.

    Program Definition e2' : [Hom ─ , s n ] ~> [Hom ─ , n ]
      := Build_Transform'
        (λ m,  {|morphism := e2_data|}
          : fobj[[Hom ─ , s n ]] m  ~{ Sets }~> fobj[[Hom ─ , n ]] m)
        _.
    Final Obligation.
      induction n using UWCwFN_ind.
      + now rewrite !e2_data_beta_distobj, <-pi1_comp.
      + rewrite !e2_data_beta_s.
        now rewrite snoc_comp, <-pi1_comp, pi2_subst, (IHo (π1 _)).
    Qed.

    Definition e1e2 : [Hom ─ , s n ] ⟹ Tm × [Hom ─ , n ]
      := e1' △ e2'.

  End flpctxcomp_naturality.

  Section flpctxcomp_iso.

    Context ( n : C).

    Program Definition flpctxcmp : Tm × [Hom ─ , n ] ≅ [Hom ─ , s n ] :=
    {|
      to := cons';
      from := e1e2;
    |}.
    Next Obligation.
      rewrite id_right.
      induction n using UWCwFN_ind.
      - rewrite e1_data_beta_distobj, e2_data_beta_distobj, cons_data_beta_distobj.
        now rewrite <-snoc_eta.
      - rewrite e1_data_beta_s, e2_data_beta_s, cons_data_beta_s, pi1_snoc, pi2_snoc.
        now rewrite IHo, <-snoc_eta. 
    Qed.
    Final Obligation.
      split.
      - induction n using UWCwFN_ind.
        + rewrite e1_data_beta_distobj, cons_data_beta_distobj.
          rewrite pi2_snoc.
          symmetry.
          refine (fmap_id (Functor := Tm) c).
        + rewrite e1_data_beta_s, cons_data_beta_s, pi1_snoc.
          refine (IHo (π1 _)).
      - induction n using UWCwFN_ind.
        + rewrite e2_data_beta_distobj, cons_data_beta_distobj.
          now rewrite pi1_snoc, id_right.
        + rewrite e2_data_beta_s, cons_data_beta_s, pi1_snoc, pi2_snoc.
          rewrite (IHo (π1 _)).
          now rewrite !id_right, <-snoc_eta.
    Qed.

  End flpctxcomp_iso.

End FlippedComprehension_def.

Definition cons {C : UWCwFN} {m n : C} (aδ : (Tm m) * (m ~> n))
  : (m ~> s n)
  := (to (flpctxcmp _ _) _ aδ).

Definition e1 {C : UWCwFN} {m n : C} (δ : m ~> s n)
  : Tm m
  := exl (C:=Sets) ((flpctxcmp _ _)⁻¹ _ δ).
Instance proper_e1 {C : UWCwFN} {m n:C} : (Proper (equiv ==> equiv) (@π2 _ m n)).
Proof.
  intros ? ? E.
  unfold π2.
  now rewrite E.
Qed.

Definition e2 {C : UWCwFN} {m n : C} (δ : m ~> s n)
  : m ~> n
  := exr (C:=Sets) ((flpctxcmp _ _)⁻¹ _ δ).
Instance proper_e2 {C : UWCwFN} {m n:C} : (Proper (equiv ==> equiv) (@π1 _ m n)).
Proof.
  intros ? ? E.
  unfold π1.
  now rewrite E.
Qed.

(* 
  e1 δ, e1_data _ δ, e1' _ _ δ are all judgmentally equal and convertible.
  Same for e2
*)

Ltac unfold_uwcwf_notation := unfold e1, e2, π1, π2, subst.

Section FlippedComprehension_DefProperties.

Context {C: UWCwFN} {m n : C}.

Section naturality.
Context {l : C} (γ : l ~> m).

Lemma cons_comp (δ : m ~> n) (a : Tm m)
  : cons (a,δ)  ∘ γ ≈ cons (a[γ],δ ∘ γ).
Proof. apply (naturality (to (flpctxcmp C n)) _ _ γ (a,δ)). Qed.
Lemma e1_subst (δ : m ~> s n)
  : (e1 δ)[γ] ≈ e1 (δ ∘ γ).
Proof. apply (naturality (from (flpctxcmp C n)) _ _ γ δ). Qed.
Lemma e2_comp (δ : m ~> s n)
  : (e2 δ) ∘ γ ≈ e2 (δ ∘ γ).
Proof. apply (naturality (from (flpctxcmp C n)) _ _ γ δ). Qed.

End naturality.

Section isomorphism.
Lemma e1_cons (δ : m ~> n) (a : Tm m)
  : e1 (cons(a , δ)) ≈ a.
Proof.
  unfold_uwcwf_notation.
  rewrite (iso_from_to (flpctxcmp C n) m (a,δ)).
  apply ((@fmap_id _ _ Tm _) a).
Qed.
Lemma e2_cons (δ : m ~> n) (a : Tm m)
  : e2 (cons(a,δ)) ≈ δ.
Proof.
  unfold_uwcwf_notation.
  rewrite (iso_from_to (flpctxcmp C n) m (a,δ)).
  simpl; now rewrite id_right.
Qed.

Lemma cons_eta (δ : m ~> s n)
  : δ ≈ cons (e1 δ,e2 δ).
Proof.
  spose (iso_to_from (flpctxcmp C n) m δ) as X.
  revert X.
  cat.
Qed.

End isomorphism.

Notation "↓[ n ]" := (e2 id[s n]).

End FlippedComprehension_DefProperties.

(*
  The Flipped Comprehension construction gives another uwCwFN with
  the same underlying substitution and term sets
*)
Section FlippedComprehension_uwCwFN.
  Context (C:UWCwFN).

  Definition flpctxcmp_asctxcmp (n:C) : 
    fobj[Curried_CoHom C] n × Tm ≅ fobj[Curried_CoHom C] (ctxext n)
    := (flpctxcmp _ _) ⊙ prod_comm.


  Definition flpctxcmp_UnitypedWeakCwF : @UnitypedWeakCwF C
    := {|
      distobj := ⋆_C;
      ctxext := ctxext;
      ctxcmp := flpctxcmp_asctxcmp |}.

  Definition flpctxcmp_UWCwF : UWCwF
    := (UWCwF_incl (UWCwFN_incl C);flpctxcmp_UnitypedWeakCwF).
  
  Program Definition flpctxcmp_NaturalNumberProperty : NaturalNumberProperty flpctxcmp_UWCwF
    := {|
      nnp_l := λ Γ, nnp_l (Γ:C)
    |}.
  Next Obligation.
    intro Γ.
    change obj[C] in Γ.
    exact (nnp_cl' Γ).
  Qed.
  Final Obligation.
    intro l.
    exact (nnp_lc l).
  Qed.
  
  Definition flpctxcmp_UWCwFN : UWCwFN
  := (flpctxcmp_UWCwF;flpctxcmp_NaturalNumberProperty).

End FlippedComprehension_uwCwFN.