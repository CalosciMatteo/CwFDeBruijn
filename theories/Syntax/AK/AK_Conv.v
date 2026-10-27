From Stdlib Require Export Relations.

From CwFdeBruijn.Syntax.Setup Require Export RelationsLemmas.
From CwFdeBruijn.Syntax.AK Require Export AK.
From CwFdeBruijn.Syntax.AKcf Require Export AKcf_Conv.

Declare Scope AK.
Delimit Scope AK with AK.
Open Scope AK.

Reserved Notation " x '-->' x' " (at level 55, x' at level 55).
Reserved Notation " x '--s>' x' " (at level 55, x' at level 55).

Inductive toTms_compatible
  (R : forall p  , relation (Tm p))
  (Rs: forall p q, relation (Tms p q))
  : forall p q, relation (Tms p q) :=
  | srefl {p q} {δ' δ : Tms p q}
    : Rs p q δ' δ
    -> toTms_compatible R Rs p q δ' δ
  | snoc_Tms_prpg {p q} {δ' δ : Tms p q} {x : Tm p}
    : toTms_compatible R Rs p q δ' δ ->
      toTms_compatible R Rs p (S q) (Tms_snoc δ' x) (Tms_snoc δ x)
  | snoc_Tm_prpg {p q} {x' x : Tm p} {δ : Tms p q}
    : toTm_compatible R Rs p x' x ->
      toTms_compatible R Rs p (S q) (Tms_snoc δ x') (Tms_snoc δ x)
  | compl_prpg {p q r} {δ' δ : Tms r q} {σ : Tms p r}
    : toTms_compatible R Rs r q δ' δ -> toTms_compatible R Rs p q (Tms_comp δ' σ) (Tms_comp δ σ)
  | compr_prpg {p q r} {σ' σ : Tms p r} {δ : Tms r q}
    : toTms_compatible R Rs p r σ' σ -> toTms_compatible R Rs p q (Tms_comp δ σ') (Tms_comp δ σ)
  | π₁_prpg {p q} {δ' δ : Tms p (S q)}
    : toTms_compatible R Rs p (S q) δ' δ ->
      toTms_compatible R Rs p q (Tms_π₁ δ') (Tms_π₁ δ)
with toTm_compatible
  (R : forall p  , relation (Tm p))
  (Rs: forall p q, relation (Tms p q))
  : forall p, relation (Tm p) :=
  | refl {p} {x' x : Tm p}
    : R p x' x
    -> toTm_compatible R Rs p x' x
  | subst_Tm_prpg {p q} {x' x : Tm q} {δ : Tms p q}
    : toTm_compatible R Rs q x' x ->
      toTm_compatible R Rs p (Tm_subst x' δ) (Tm_subst x δ)
  | subst_Tms_prpg {p q} {δ' δ : Tms p q} {x : Tm q}
    : toTms_compatible R Rs p q δ' δ ->
      toTm_compatible R Rs p (Tm_subst x δ') (Tm_subst x δ)
  | π₂_prpg {p q} {δ' δ : Tms p (S q)}
    : toTms_compatible R Rs p (S q) δ' δ ->
      toTm_compatible R Rs p (Tm_π₂ δ') (Tm_π₂ δ)
  | rand_prpg {p} {x' x y: Tm p}
    : toTm_compatible R Rs p x' x ->
      toTm_compatible R Rs p (Tm_app x' y) (Tm_app x y)
  | rator_prpg {p} {x y' y : Tm p}
    : toTm_compatible R Rs p y' y ->
      toTm_compatible R Rs p (Tm_app x y') (Tm_app x y)
  | lam_prpg {p} {x' x : Tm (S p)}
    : toTm_compatible R Rs (S p) x' x ->
      toTm_compatible R Rs p (Tm_lam x') (Tm_lam x).

Ltac onestepf := apply rst_step; try apply refl; try apply srefl.
Ltac onestepb := apply rst_sym; apply rst_step; try apply refl; try apply srefl.

Inductive Tmsλstep' : forall p q, relation (Tms p q) := .

Inductive Tmλstep' : forall p, relation (Tm p) :=
  | Tm_beta {p} {t: Tm (S p)} {x : Tm p}
    : Tmλstep' p
      (Tm_app (Tm_lam t) x)
      (Tm_subst t (Tms_snoc (Tms_id p) x))
  | Tm_eta {p} {t : Tm p}
    : Tmλstep' p
      (Tm_lam (Tm_app
        (Tm_subst t (Tms_π₁ (Tms_id (S p))))
        (Tm_π₂ (Tms_id (S p)))))
      t.

Definition Tmsλstep := toTms_compatible (Tmλstep') Tmsλstep'.
Notation " x '⩶s>' x' " := (Tmsλstep _ _ x x') : AK.
Definition Tmλstep := toTm_compatible (Tmλstep') Tmsλstep'.
Notation " x '⩶>' x' " := (Tmλstep _ x x') : AK.

Definition Tmsλconv {p q} := clos_refl_trans (Tms p q) (Tmsλstep p q).
Notation " x '⩶s>*' x' " := (Tmsλconv x x') (at level 55, x' at level 55) : AK.
Definition Tmλconv {p} := clos_refl_trans (Tm p) (Tmλstep p).
Notation " x '⩶>*' x' " := (Tmλconv x x') (at level 55, x' at level 55) : AK.

Definition Tmsλeq {p q} := clos_refl_sym_trans (Tms p q) (Tmsλstep p q).
Notation " x '<⩶s>*' x' " := (Tmsλeq x x') (at level 55, x' at level 55) : AK.
Definition Tmλeq {p} := clos_refl_sym_trans (Tm p) (Tmλstep p).
Notation " x '<⩶>*' x' " := (Tmλeq x x') (at level 55, x' at level 55) : AK.

Inductive Tmsσstep' : forall p q, relation (Tms p q) :=
  | idl {q} {p} {δ : Tms p q}
    : (Tms_comp (Tms_id q) δ) --s> δ
  | idr {p} {q} {δ : Tms p q}
    : (Tms_comp δ (Tms_id p)) --s> δ
  | ass {r s} {σ : Tms r s} {q} {δ : Tms q r} {p} {ν : Tms p q}
    : Tms_comp (Tms_comp σ δ) ν --s> Tms_comp σ (Tms_comp δ ν)
  | snocomp {p q} {δ : Tms p q} {t : Tm p} {r} {σ : Tms r p }
    : (Tms_comp (Tms_snoc δ t) σ) --s> (Tms_snoc (Tms_comp δ σ) (Tm_subst t σ))
  | π₁beta {p q} {δ : Tms p q} {t : Tm p}
    : Tms_π₁ (Tms_snoc δ t) --s> δ
  | πeta {p q} {δ : Tms p (S q)} : Tms_snoc (Tms_π₁ δ) (Tm_π₂ δ) --s> δ
  | nileta {p} {σ : Tms p 0} : σ --s> Tms_nil p
where " δ '--s>' δ' " := (Tmsσstep' _ _ δ δ')
with Tmσstep' : forall p, relation (Tm p) :=
  | idsubst {p} {t : Tm p}
    : (Tm_subst t (Tms_id p)) --> t
  | substsubst {p q} {σ : Tms p q} {r} {δ : Tms q r} {t : Tm r}
    : (Tm_subst (Tm_subst t δ) σ) --> (Tm_subst t (Tms_comp δ σ))
  | π₂beta {p q} {δ : Tms p q} {t : Tm p}
    : Tm_π₂ (Tms_snoc δ t) --> t
  | lamsubst {p q} {δ : Tms p q} {t : Tm (S q)}
    : Tm_subst (Tm_lam t) δ -->
      Tm_lam (Tm_subst t (Tms_snoc (Tms_comp δ (Tms_π₁ (Tms_id (S p)))) (Tm_π₂ (Tms_id (S p)))))
  | appsubst {p q} {δ : Tms p q} {x y : Tm q}
    : Tm_subst (Tm_app x y) δ -->
      Tm_app (Tm_subst x δ) (Tm_subst y δ)
where " x '-->' x' " := (Tmσstep' _ x x').


Definition Tmσstep := toTm_compatible ( @Tmσstep' ) ( @Tmsσstep' ).
Definition Tmsσstep := toTms_compatible ( @Tmσstep' ) ( @Tmsσstep' ).

Definition Tmσconv {p} := clos_refl_trans (Tm p) (Tmσstep p).
Notation " x '-->*' x' " := (Tmσconv x x') (at level 55, x' at level 55) : AK.
Definition Tmsσconv {p q} := clos_refl_sym_trans (Tms p q) (Tmsσstep p q).
Notation " x '--s>*' x' " := (Tmsσconv x x') (at level 55, x' at level 55) : AK.

Definition Tmσeq {p} := clos_refl_sym_trans (Tm p) (Tmσstep p).
Notation " x '<-->*' x' " := (Tmσeq x x') (at level 55, x' at level 55) : AK.
Definition Tmsσeq {p q} := clos_refl_sym_trans (Tms p q) (Tmsσstep p q).
Notation " x '<--s>*' x' " := (Tmsσeq x x') (at level 55, x' at level 55) : AK.

Record AK_compatible  (R : forall {p}, Tm p -> Tm p -> Prop) (Rs : forall {p q}, Tms p q -> Tms p q -> Prop) := make_AK_compatible {
  snoc_Tms_step_compatibility {p q} {δ' δ : Tms p q} {x : Tm p}
    : Rs δ' δ -> Rs (Tms_snoc δ' x) (Tms_snoc δ x);
  snoc_Tm_step_compatibility {p} {x' x : Tm p} {q} {δ : Tms p q}
    : R x' x -> Rs (Tms_snoc δ x') (Tms_snoc δ x);
  compl_step_compatibility {q r} {δ' δ : Tms q r} {p} {σ : Tms p q}
    : Rs δ' δ -> Rs (Tms_comp δ' σ) (Tms_comp δ σ);
  compr_step_compatibility {p q} {σ' σ : Tms p q} {r} {δ : Tms q r}
    : Rs σ' σ -> Rs (Tms_comp δ σ') (Tms_comp δ σ);
  π₁_step_compatibility {p q} {δ' δ : Tms p (S q)}
    : Rs δ' δ -> Rs (Tms_π₁ δ') (Tms_π₁ δ);
  subst_Tm_step_compatibility {q} {x' x : Tm q} {p} {δ : Tms p q}
    : R x' x -> R (Tm_subst x' δ) (Tm_subst x δ);
  subst_Tms_step_compatibility {p q} {δ' δ : Tms p q} {x : Tm q}
    : Rs δ' δ -> R (Tm_subst x δ') (Tm_subst x δ);
  π₂_step_compatibility {p q} {δ' δ : Tms p (S q)}
    : Rs δ' δ -> R (Tm_π₂ δ') (Tm_π₂ δ);
  rator_step_compatibility {p} {x' x y : Tm p}
    : R x' x -> R (Tm_app x' y) (Tm_app x y);
  rand_step_compatibility {p} {x y' y : Tm p}
    : R y' y -> R (Tm_app x y') (Tm_app x y);
  lam_step_compatibility {p} {x' x : Tm (S p)}
    : R x' x -> R (Tm_lam x') (Tm_lam x);
}.

Create HintDb AK.
#[export] Hint Unfold Tmλstep : AK.
#[export] Hint Unfold Tmsλstep : AK.
#[export] Hint Unfold Tmλconv : AK.
#[export] Hint Unfold Tmsλconv : AK.
#[export] Hint Unfold Tmλeq : AK.
#[export] Hint Unfold Tmsλeq : AK.
#[export] Hint Unfold Tmσstep : AK.
#[export] Hint Unfold Tmsσstep : AK.
#[export] Hint Unfold Tmσeq : AK.
#[export] Hint Unfold Tmsσeq : AK.
#[export] Hint Constructors Tmsλstep' : AK.
#[export] Hint Constructors Tmλstep' : AK.
#[export] Hint Constructors toTms_compatible Tmλstep' Tmsλstep' : AK.
#[export] Hint Constructors toTm_compatible Tmλstep' Tmsλstep' : AK.
#[export] Hint Constructors Tmsσstep' : AK.
#[export] Hint Constructors Tmσstep' : AK.
#[export] Hint Constructors toTms_compatible Tmσstep' Tmsσstep' : AK.
#[export] Hint Constructors toTm_compatible Tmσstep' Tmsσstep' : AK.

Theorem AKλstep_compatibility : AK_compatible ( @Tmλstep ) ( @Tmsλstep ).
Proof.
  apply make_AK_compatible; auto with AK.
Qed.

Theorem AKλconv_compatibility : AK_compatible ( @Tmλconv ) ( @Tmsλconv ).
Proof.
  apply make_AK_compatible; intros.
  all: try (
    (apply (rt_compatibility ( @Tmsλstep _ _ ) (@Tmsλstep _ _ ))) ||
    (apply (rt_compatibility ( @Tmλstep _ )    (@Tmsλstep _ _ ))) ||
    (apply (rt_compatibility ( @Tmλstep _ )    (@Tmλstep _ ))) ||
    (apply (rt_compatibility ( @Tmsλstep _ _ ) (@Tmλstep _ )))).
  all: auto with AK sets.
  - apply (rt_compatibility ( @Tmsλstep _ _) ( @Tmsλstep _ _)
      (fun δ => Tms_snoc δ x)); auto with AK sets.
  - apply (rt_compatibility ( @Tmsλstep _ _) ( @Tmsλstep _ _)
      (fun δ => Tms_comp δ σ )); auto with AK sets.
  - apply (rt_compatibility ( @Tmλstep _ ) ( @Tmλstep _ )
      (fun x => Tm_subst x δ)); auto with AK sets.
  - apply (rt_compatibility ( @Tmλstep _ ) ( @Tmλstep _ ) (fun x => Tm_app x y)); auto with AK sets.
Qed.

Theorem AKλeq_compatibility : AK_compatible ( @Tmλeq ) ( @Tmsλeq ).
Proof.
  apply make_AK_compatible; intros.
  all: try (
    (apply (rst_compatibility ( @Tmsλstep _ _ ) (@Tmsλstep _ _ ))) ||
    (apply (rst_compatibility ( @Tmλstep _ )    (@Tmsλstep _ _ ))) ||
    (apply (rst_compatibility ( @Tmλstep _ )    (@Tmλstep _ ))) ||
    (apply (rst_compatibility ( @Tmsλstep _ _ ) (@Tmλstep _ )))
  ).
  all: auto with AK sets.
  - apply (rst_compatibility ( @Tmsλstep _ _) ( @Tmsλstep _ _)
      (fun δ => Tms_snoc δ x)); auto with AK sets.
  - apply (rst_compatibility ( @Tmsλstep _ _) ( @Tmsλstep _ _)
      (fun δ => Tms_comp δ σ)); auto with AK sets.
  - apply (rst_compatibility ( @Tmλstep _ ) ( @Tmλstep _ )
      (fun x => Tm_subst x δ)); auto with AK sets.
  - apply (rst_compatibility ( @Tmλstep _ ) ( @Tmλstep _ ) (fun x => Tm_app x y)); auto with AK sets.
Qed.

Theorem AKσstep_compatibility : AK_compatible ( @Tmσstep ) ( @Tmsσstep ).
Proof.
  apply make_AK_compatible; auto with AK.
Qed.

Theorem AKσeq_compatibility : AK_compatible ( @Tmσeq ) ( @Tmsσeq ).
Proof.
  apply make_AK_compatible; intros; induction H; try auto with sets AK.
  - eapply rst_trans with (Tms_snoc y x); assumption.
  - eapply (rst_trans _ _ _  (Tms_snoc δ y)); assumption.
  - eapply (rst_trans _ _ _  (Tms_comp y σ)); assumption.
  - eapply (rst_trans _ _ _  (Tms_comp δ y)); assumption.
  - eapply (rst_trans _ _ _  (Tms_π₁ y)); assumption.
  - eapply (rst_trans _ _ _  (Tm_subst y δ)); assumption.
  - eapply (rst_trans _ _ _  (Tm_subst x y)); assumption.
  - eapply (rst_trans _ _ _  (Tm_π₂ y)); assumption.
  - eapply (rst_trans _ _ _  (Tm_app y0 y)); assumption.
  - eapply (rst_trans _ _ _  (Tm_app x y)); assumption.
  - eapply (rst_trans _ _ _  (Tm_lam y)); assumption.
Qed.

Definition HINTsnoc_Tms_step_compatibility {p q} {δ' δ : Tms p q} {x : Tm p} (H : δ' <--s>* δ) : (Tms_snoc δ' x) <--s>* (Tms_snoc δ x) := snoc_Tms_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (x:=x) H.
Definition HINTsnoc_Tm_step_compatibility {p q} {x' x : Tm p} {δ : Tms p q} (H : x' <-->* x ) : (Tms_snoc δ x') <--s>* (Tms_snoc δ x) := snoc_Tm_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (δ:=δ) H.
Definition HINT_compl_step_compatibility {p q r} {δ' δ : Tms r q} {σ : Tms p r} (H : δ' <--s>* δ) : (Tms_comp δ' σ) <--s>* (Tms_comp δ σ) := compl_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (σ:=σ) H .
Definition HINT_compr_step_compatibility {p q r} {σ' σ : Tms p r} {δ : Tms r q} (H : σ' <--s>* σ) : (Tms_comp δ σ') <--s>* (Tms_comp δ σ) := compr_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (δ:=δ) H.
Definition HINT_π₁_step_compatibility {p q} {δ' δ : Tms p (S q)} (H : δ' <--s>* δ) : (Tms_π₁ δ') <--s>* (Tms_π₁ δ) := π₁_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility H.
Definition HINTsubst_Tm_step_compatibility {p q} {x' x : Tm q} {δ : Tms p q} (H : x' <-->* x ) : (Tm_subst x' δ) <-->* (Tm_subst x δ) := subst_Tm_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (δ:=δ) H.
Definition HINTsubst_Tms_step_compatibility {p q} {δ' δ : Tms p q} {x : Tm q} (H : δ' <--s>* δ) : (Tm_subst x δ') <-->* (Tm_subst x δ) := subst_Tms_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility (x:=x) H.
Definition HINT_π₂_step_compatibility {p q} {δ' δ : Tms p (S q) } (H : δ' <--s>* δ) : (Tm_π₂ δ') <-->* (Tm_π₂ δ) := π₂_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility H.
Definition HINT_rator_step_compatibility {p} {x' x y : Tm p} (H : x' <-->* x ) : (Tm_app x' y) <-->* (Tm_app x y) := rator_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility H.
Definition HINT_rand_step_compatibility {p} {x y' y : Tm p} (H : y' <-->* y ) : (Tm_app x y') <-->* (Tm_app x y) := rand_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility H.
Definition HINT_lam_step_compatibility {p} {x' x : Tm (S p)} (H : x' <-->* x ) : (Tm_lam x') <-->* (Tm_lam x) := lam_step_compatibility ( @Tmσeq ) ( @Tmsσeq ) AKσeq_compatibility H.

#[export] Hint Resolve HINTsnoc_Tms_step_compatibility  : AK.
#[export] Hint Resolve HINTsnoc_Tm_step_compatibility : AK.
#[export] Hint Resolve HINT_compl_step_compatibility : AK.
#[export] Hint Resolve HINT_compr_step_compatibility : AK.
#[export] Hint Resolve HINT_π₁_step_compatibility : AK.
#[export] Hint Resolve HINTsubst_Tm_step_compatibility : AK.
#[export] Hint Resolve HINTsubst_Tms_step_compatibility : AK.
#[export] Hint Resolve HINT_π₂_step_compatibility : AK.
#[export] Hint Resolve HINT_rator_step_compatibility : AK.
#[export] Hint Resolve HINT_rand_step_compatibility : AK.
#[export] Hint Resolve HINT_lam_step_compatibility : AK.

Lemma app_parallelcompatibility
  (R : forall {p}, Tm p -> Tm p -> Prop)
  (Rs : forall {p q}, Tms p q -> Tms p q -> Prop)
  (trans_R : forall p, Relation_Definitions.transitive _ (@R p))
  (H : AK_compatible (@R) (@Rs))
  {p} {x x' y y' : Tm p}
  : R x' x -> R y' y -> R (Tm_app x' y') (Tm_app x y).
Proof.
  intros red_x red_y.
  eapply trans_R.
  - eapply (rator_step_compatibility _ _ H).
    exact red_x.
  - eapply (rand_step_compatibility _ _ H).
    exact red_y.
Qed.

(* Derived equalities *)
Lemma substπ₂ {p q r} {δ : Tms p q} {σ : Tms q (S r)}
  : (Tm_subst (Tm_π₂ σ) δ) <-->* (Tm_π₂ (Tms_comp σ δ)).
Proof.
  apply rst_sym.
  eapply rst_trans.
  { eapply HINT_π₂_step_compatibility.
    eapply HINT_compl_step_compatibility.
    onestepb.
    apply πeta. }
  eapply rst_trans.
  { eapply HINT_π₂_step_compatibility.
    onestepf. apply snocomp. }
  auto with AK sets.
Qed.

Lemma π₁comp {p q r} {δ : Tms r (S q)} {σ : Tms p r }
    : (Tms_comp (Tms_π₁ δ) σ) <--s>* (Tms_π₁ (Tms_comp δ σ)).
Proof.
  apply rst_sym.
  eapply rst_trans.
  { eapply HINT_π₁_step_compatibility.
    eapply HINT_compl_step_compatibility.
    onestepb.
    apply πeta. }
  eapply rst_trans.
  { eapply HINT_π₁_step_compatibility.
    onestepf. apply snocomp. }
  auto with AK sets.
Qed. 

Close Scope AK.