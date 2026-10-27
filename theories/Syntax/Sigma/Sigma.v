From CwFdeBruijn.Syntax Require Export Setup Setup.GenRewr Setup.RelationsLemmas.
Require Import Setoid Morphisms RelationClasses.


(* AS: Abadi σ calculus *)

Inductive TmsAS : Type :=
| TmsAS_id : TmsAS
| TmsAS_S : TmsAS
| TmsAS_snoc (δ : TmsAS) (a : TmAS) : TmsAS
| TmsAS_comp (δ₁ : TmsAS) (δ₂ : TmsAS) : TmsAS
with TmAS : Type :=
| TmAS_0 : TmAS
| TmAS_app (a : TmAS) (b : TmAS) : TmAS
| TmAS_subst (a : TmAS) (δ : TmsAS) : TmAS
| TmAS_lam (a : TmAS) : TmAS.

Lemma deceq_TmsAS : forall (δ σ : TmsAS), {δ = σ} + {δ <> σ}
with deceq_TmAS : forall (a b : TmAS), {a = b} + {a <> b}.
Proof.
  all:
    decide equality.
Defined.

Declare Scope AS_scope.
Delimit Scope AS_scope with AS.

Notation "'id'" := (TmsAS_id) (at level 5) : AS_scope.
Notation "'S'" := (TmsAS_S) (at level 5) : AS_scope.
Notation "'<' δ ',' a '>'" := (TmsAS_snoc δ a) (δ at level 40, a at level 40) : AS_scope.
Notation "δ₁ '○' δ₂" := (TmsAS_comp δ₁ δ₂) (at level 9) : AS_scope.
Notation "'0'" := (TmAS_0) : AS_scope.
Notation "a '@' b" := (TmAS_app a b) (at level 9)  : AS_scope.
Notation "a '[' δ ']'" := (TmAS_subst a δ) (at level 9, δ at level 200)  : AS_scope.
Notation "'λ' a" := (TmAS_lam a) (at level 40)  : AS_scope.


Open Scope AS_scope.

Definition lift (δ:TmsAS) : TmsAS :=
  < δ ○ S , 0 >.

Inductive TmsASσstep' : relation TmsAS :=
| AS_idl {δ : TmsAS}
  : TmsASσstep' (TmsAS_id ○ δ) δ
| AS_Sid
  : TmsASσstep' (S ○ (TmsAS_id)) S
| AS_Ssnoc {δ : TmsAS} {t : TmAS}
  : TmsASσstep' (S ○ <δ,t>) δ
| AS_snocomp {δ : TmsAS} {t : TmAS} {σ : TmsAS}
  : TmsASσstep' (<δ,t> ○ σ) <δ ○ σ,(t[σ])>
| AS_ass {σ : TmsAS} {δ : TmsAS} {ν : TmsAS}
  : TmsASσstep' ((σ ○ δ) ○ ν) (σ ○ (δ ○ ν))
(* Eta rules, not present in [Abadi] *)
| AS_etaid : TmsASσstep' <S,0> id
| AS_eta {δ}: TmsASσstep' <S ○ δ , 0[δ]> δ.
Inductive TmASσstep' : relation TmAS :=
| AS_0id
  : TmASσstep' (0 [id]) 0
| AS_0snoc {δ : TmsAS} {t : TmAS}
  : TmASσstep' (0 [<δ,t>]) t
| AS_appsubst {x y: TmAS} {δ: TmsAS}
  : TmASσstep' ((x @ y) [δ])
      ((x[δ]) @ (y[δ]))
| AS_lamsubst {δ : TmsAS} {t : TmAS}
  : TmASσstep' ((λ t) [δ]) (λ (t [lift δ]))
| AS_substsubst {σ : TmsAS} {δ : TmsAS} {t : TmAS}
  : TmASσstep' (t [δ] [σ]) (t [δ ○ σ]).

Inductive toTmsAS_compatible (R:relation TmAS) (Rs:relation TmsAS)
  : relation TmsAS :=
| AS_srefl {δ' δ : TmsAS}
  : Rs δ' δ -> toTmsAS_compatible R Rs δ' δ
| snoc_TmsAS_prpg {δ' δ : TmsAS} {x : TmAS}
  : toTmsAS_compatible R Rs δ' δ -> toTmsAS_compatible R Rs <δ',x> <δ,x>
| snoc_TmAS_prpg {x' x : TmAS} {δ : TmsAS}
  : toTmAS_compatible R Rs x' x -> toTmsAS_compatible R Rs <δ,x'> <δ,x>
| AS_compl_prpg {δ' δ : TmsAS} {σ : TmsAS}
  : toTmsAS_compatible R Rs δ' δ -> toTmsAS_compatible R Rs (δ' ○ σ) (δ ○ σ)
| AS_compr_prpg {σ' σ : TmsAS} {δ : TmsAS}
  : toTmsAS_compatible R Rs σ' σ -> toTmsAS_compatible R Rs (δ ○ σ') (δ ○ σ)
with toTmAS_compatible (R:relation TmAS) (Rs:relation TmsAS)
  : relation TmAS :=
| AS_refl {x' x : TmAS}
  : R x' x
  -> toTmAS_compatible R Rs x' x
| subst_TmAS_prpg {x' x : TmAS} {δ : TmsAS}
  : toTmAS_compatible R Rs x' x ->
    toTmAS_compatible R Rs (x' [δ]) (x [δ])
| subst_TmsAS_prpg {δ' δ : TmsAS} {x : TmAS}
  : toTmsAS_compatible R Rs δ' δ ->
    toTmAS_compatible R Rs (x [δ']) (x [δ])
| AS_rand_prpg {x' x y: TmAS}
  : toTmAS_compatible R Rs x' x ->
    toTmAS_compatible R Rs (x' @ y) (x @ y)
| AS_rator_prpg {x y' y : TmAS}
  : toTmAS_compatible R Rs y' y ->
    toTmAS_compatible R Rs (x @ y') (x @ y)
| AS_lam_prpg {x' x : TmAS}
  : toTmAS_compatible R Rs x' x ->
    toTmAS_compatible R Rs (λ x') (λ x).

Ltac onestep := apply rt_step; try apply AS_refl; try apply AS_srefl.

Definition TmsASσstep := toTmsAS_compatible TmASσstep' TmsASσstep'.
Notation " δ '--s>' δ' " := (TmsASσstep δ δ') (at level 55, δ' at level 55) : AS_scope.

Definition TmASσstep := toTmAS_compatible TmASσstep' TmsASσstep'.
Notation " x '-->' x' " := (TmASσstep x x') (at level 55, x' at level 55): AS_scope.

Definition TmASσconv := clos_refl_trans (TmAS) (TmASσstep).
Notation " x '-->*' x' " := (TmASσconv x x') (at level 55, x' at level 55) : AS_scope.

Definition TmsASσconv := clos_refl_trans (TmsAS) (TmsASσstep).
Notation " x '--s>*' x' " := (TmsASσconv x x') (at level 55, x' at level 55) : AS_scope.

Definition TmASσeq := clos_refl_sym_trans (TmAS) (TmASσstep).
Notation " x '<-->*' x' " := (TmASσeq x x') (at level 55, x' at level 55) : AS_scope.

Definition TmsASσeq := clos_refl_sym_trans (TmsAS) (TmsASσstep).
Notation " x '<--s>*' x' " := (TmsASσeq x x') (at level 55, x' at level 55) : AS_scope.


(* Setup for generalized rewriting *)
Section GeneralizedRewriting.

Global Instance TmsAS_σstep'_σstep_subrelation : subrelation TmsASσstep' TmsASσstep.
Proof. intros ? ?. apply AS_srefl. Qed.
Global Instance TmsAS_σstep_σconv_subrelation : subrelation TmsASσstep TmsASσconv.
Proof. apply rt_subrelation. Qed.
Global Instance TmsAS_σconv_σeq_subrelation : subrelation TmsASσconv TmsASσeq.
Proof. apply clos_rt_clos_rst. Qed.

Global Instance TmsAS_σstep_σeq_subrelation : subrelation TmsASσstep TmsASσeq.
Proof. apply rst_subrelation. Qed.
Global Instance TmsAS_σstep'_σconv_subrelation : subrelation TmsASσstep' TmsASσconv.
Proof.
  intros ? ? ?.
  apply rt_subrelation.
  apply AS_srefl.
  exact H.
Qed.

Global Instance TmAS_σstep'_σstep_subrelation : subrelation TmASσstep' TmASσstep.
Proof. intros ? ?. apply AS_refl. Qed.
Global Instance TmAS_σstep_σconv_subrelation : subrelation TmASσstep TmASσconv.
Proof. apply rt_subrelation. Qed.
Global Instance TmAS_σconv_σeq_subrelation : subrelation TmASσconv TmASσeq.
Proof. apply clos_rt_clos_rst. Qed.

Global Instance TmAS_σstep_σeq_subrelation : subrelation TmASσstep TmASσeq.
Proof. apply rst_subrelation. Qed.
Global Instance TmAS_σstep'_σconv_subrelation : subrelation TmASσstep' TmASσconv.
Proof.
  intros ? ? ?.
  apply rt_subrelation.
  apply AS_refl.
  exact H.
Qed.

(* Compatibility instances *)

Global Instance TmsAS_snoc_σstep_eq_σconv : Proper (TmsASσstep ==> eq ==> TmsASσconv) TmsAS_snoc.
Proof. intros ? ? H ? ? []; apply rt_step; apply (snoc_TmsAS_prpg _ _ H). Qed.
Global Instance TmsAS_snoc_eq_σstep_σconv : Proper (eq ==> TmASσstep ==> TmsASσconv) TmsAS_snoc.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (snoc_TmAS_prpg _ _ H). Qed.
Global Instance TmsAS_snoc_σconv : Proper (TmsASσconv ==> TmASσconv ==> TmsASσconv) TmsAS_snoc.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance TmsAS_comp_σstep_σrefl_σconv : Proper (TmsASσstep ==> eq ==> TmsASσconv) TmsAS_comp.
Proof. intros ? ? H ? ? []; apply rt_step; apply (AS_compl_prpg _ _ H). Qed.
Global Instance TmsAS_comp_σrefl_σstep_σconv : Proper (eq ==> TmsASσstep ==> TmsASσconv) TmsAS_comp.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (AS_compr_prpg _ _ H). Qed.
Global Instance TmsAS_comp_σconv : Proper (TmsASσconv ==> TmsASσconv ==> TmsASσconv) TmsAS_comp.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance TmAS_app_σstep_σrefl_σconv : Proper (TmASσstep ==> eq ==> TmASσconv) TmAS_app.
Proof. intros ? ? H ? ? []; apply rt_step; apply (AS_rand_prpg _ _ H). Qed.
Global Instance TmAS_app_σrefl_σstep_σconv : Proper (eq ==> TmASσstep ==> TmASσconv) TmAS_app.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (AS_rator_prpg _ _ H). Qed.
Global Instance TmAS_app_σconv : Proper (TmASσconv ==> TmASσconv ==> TmASσconv) TmAS_app.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance TmAS_subst_σstep_σrefl_σconv : Proper (TmASσstep ==> eq ==> TmASσconv) TmAS_subst.
Proof. intros ? ? H ? ? []; apply rt_step; apply (subst_TmAS_prpg _ _ H). Qed.
Global Instance TmAS_subst_σrefl_σstep_σconv : Proper (eq ==> TmsASσstep ==> TmASσconv) TmAS_subst.
Proof. intros ? ? [] ? ? H; apply rt_step; apply (subst_TmsAS_prpg _ _ H). Qed.
Global Instance TmAS_subst_σconv : Proper (TmASσconv ==> TmsASσconv ==> TmASσconv) TmAS_subst.
Proof. apply rt_lift_proper_2; apply _. Qed.

Global Instance TmsAS_lam_σstep_σconv : Proper (TmASσstep ==> TmASσconv) TmAS_lam.
Proof. intros ? ? H; apply rt_step; apply (AS_lam_prpg _ _ H). Qed.
Global Instance TmsAS_lam_σconv : Proper (TmASσconv ==> TmASσconv) TmAS_lam.
Proof. apply rt_lift_proper_1; apply _. Qed.

Global Instance TmsAS_lift_σstep_σconv : Proper (TmsASσstep ==> TmsASσconv) lift.
Proof. unfold lift; intros ? ? H; now rewrite H. Qed.
Global Instance TmsAS_lift_σconv : Proper (TmsASσconv ==> TmsASσconv) lift.
Proof. apply rt_lift_proper_1; apply _. Qed.

(* Instances for σeq *)
Instance Proper_R_eq_TmsASσeq {A B : Type} {R: relation A}
  (f : A -> B -> TmsAS)
  `{Hf : Proper _ (R ==> eq ==> TmsASσconv) f} :
  Proper (R ==> eq ==> TmsASσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ TmsASσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_eq_R_TmsASσeq {A B : Type} {R: relation B}
  (f : A -> B -> TmsAS)
  `{Hf : Proper _ (eq ==> R ==> TmsASσconv) f} :
  Proper (eq ==> R ==> TmsASσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ TmsASσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_R_eq_TmASσeq {A B : Type} {R: relation A}
  (f : A -> B -> TmAS)
  `{Hf : Proper _ (R ==> eq ==> TmASσconv) f} :
  Proper (R ==> eq ==> TmASσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ TmASσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.
Instance Proper_eq_R_TmASσeq {A B : Type} {R: relation B}
  (f : A -> B -> TmAS)
  `{Hf : Proper _ (eq ==> R ==> TmASσconv) f} :
  Proper (eq ==> R ==> TmASσeq) f.
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply (clos_rt_clos_rst _ TmASσstep).
  apply (Hf _ _ Hx _ _ Hy).
Qed.

Instance Proper_R_TmsASσeq {A : Type} {R: relation A}
  (f : A -> TmsAS)
  `{Hf : Proper _ (R ==> TmsASσconv) f} :
  Proper (R ==> TmsASσeq) f.
Proof.
  intros x1 x2 Hx.
  apply (clos_rt_clos_rst _ TmsASσstep).
  apply (Hf _ _ Hx).
Qed.
Instance Proper_R_TmASσeq {A : Type} {R: relation A}
  (f : A -> TmAS)
  `{Hf : Proper _ (R ==> TmASσconv) f} :
  Proper (R ==> TmASσeq) f.
Proof.
  intros x1 x2 Hx.
  apply (clos_rt_clos_rst _ TmASσstep).
  apply (Hf _ _ Hx).
Qed.

Global Instance TmsAS_snoc_σeq : Proper (TmsASσeq ==> TmASσeq ==> TmsASσeq) TmsAS_snoc.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance TmsAS_comp_σeq : Proper (TmsASσeq ==> TmsASσeq ==> TmsASσeq) TmsAS_comp.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance TmAS_app_σeq : Proper (TmASσeq ==> TmASσeq ==> TmASσeq) TmAS_app.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance TmAS_subst_σeq : Proper (TmASσeq ==> TmsASσeq ==> TmASσeq) TmAS_subst.
Proof. apply rst_lift_proper_2; apply _. Qed.
Global Instance TmsAS_lam_σeq : Proper (TmASσeq ==> TmASσeq) TmAS_lam.
Proof. apply rst_lift_proper_1. apply _. Qed.

Global Instance TmsAS_lift_σstep_σeq : Proper (TmsASσstep ==> TmsASσeq) lift.
Proof. unfold lift; intros ? ? H; now rewrite H. Qed.
Global Instance TmsAS_lift_σeq : Proper (TmsASσeq ==> TmsASσeq) lift.
Proof. apply rst_lift_proper_1; apply _. Qed.

End GeneralizedRewriting.

Close Scope AS_scope.