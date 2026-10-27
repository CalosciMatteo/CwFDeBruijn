From CwFdeBruijn.Syntax.Sigma Require Import Sigma substid.
Require Import Morphisms.

Open Scope AS_scope.

Lemma TmsASσstep'confluenceAt (δ : TmsAS)
  : confluenceAt TmsASσstep' TmsASσstep δ
with TmASσstep'confluenceAt (x : TmAS)
  : confluenceAt TmASσstep' TmASσstep x.
Proof.
{ intros δ1 δ2 red1 red2. 
  inversion red1; subst; inversion red2; subst; try apply confluencing_refl.
}
{ intros a1 a2 red1 red2. 
  inversion red1; subst; inversion red2; subst; try apply confluencing_refl. }
Qed.

Section Lemmas.

  Local Lemma confluencing_lift {γ δ}
  : confluencing TmsASσstep (lift δ ○ γ) ((lift δ) ○ (lift γ)).
  Proof.
  unfold confluencing, lift; esplit; split.
  - rewrite AS_ass; reflexivity.
  - now rewrite AS_snocomp, AS_0snoc, AS_ass, AS_Ssnoc.
  Qed.

  Local Lemma confluencing_snoc {δ δ' x δx}
  (H : TmsASσstep' (TmsAS_snoc δ' x) δx)
  (red_δ : δ' --s> δ)
  : confluencing TmsASσstep δx (TmsAS_snoc δ x).
  Proof.
    inversion H; subst; inversion red_δ; subst; try solve_by_inverts 2.
    - inversion H0; subst.
      + esplit; split.
        * reflexivity.
        * now rewrite AS_0id, AS_etaid.
      + esplit; split.
        2: rewrite AS_0snoc.
        all: reflexivity.
    - now rewrite H3, AS_eta.
  Qed.
  Local Lemma confluencing_snoc' {δ x' x δx}
  (H : TmsASσstep' (TmsAS_snoc δ x') δx)
  (red_x : x' --> x)
  : confluencing TmsASσstep δx (TmsAS_snoc δ x).
  Proof.
    inversion H; subst;
    inversion red_x; subst; try solve_by_inverts 2.
    - inversion H0; subst.
      + split with id; split.
        * reflexivity.
        * now rewrite AS_Sid, AS_etaid.
      + esplit; split.
        * reflexivity.
        * now rewrite AS_Ssnoc.
    - now rewrite H3, AS_eta.
  Qed.
  Local Lemma confluencing_comp {δ δ' γ δγ}
  (H : TmsASσstep' (δ' ○ γ) δγ)
  (red_δ : δ' --s> δ)
  : confluencing TmsASσstep δγ (δ ○ γ).
  Proof.
    inversion H; subst; inversion red_δ; subst; try solve_by_inverts 2.
    - inversion H0; subst.
      + now rewrite AS_eta, AS_idl.
      + now rewrite AS_ass, AS_substsubst, AS_eta.
    - now rewrite H3, AS_snocomp.
    - now rewrite H3, AS_snocomp.
    - inversion H0; subst.
      + now rewrite AS_idl.
      + now rewrite AS_idl.
      + now rewrite AS_snocomp, AS_Ssnoc.
      + now rewrite !AS_snocomp, AS_ass, AS_substsubst.
      + now rewrite !AS_ass.
    - now rewrite H3, AS_ass.
    - now rewrite H3, AS_ass.       
  Qed.
  Local Lemma confluencing_comp' {δ γ γ' δγ}
  (H : TmsASσstep' (δ ○ γ') δγ)
  (red_γ : γ' --s> γ)
  : confluencing TmsASσstep δγ (δ ○ γ).
  Proof.
    inversion H; subst; inversion red_γ; subst.
    all: try now rewrite H0, AS_idl.
    all: try now rewrite H0, AS_snocomp.
    all: try now rewrite H0, AS_ass.
    - inversion H0.
    - inversion H0.
      + now rewrite AS_idr.
      + reflexivity.
    - now rewrite H3, AS_Ssnoc.
    - now rewrite AS_Ssnoc.
  Qed.
  Local Lemma confluencing_subst {x' x δ xδ}
  (H : TmASσstep' (x'[δ]) xδ)
  (red_x : x' --> x)
  : confluencing TmASσstep xδ (x[δ]).
  Proof.
    inversion H; subst; inversion red_x; subst; try solve_by_invert.
    all: try now rewrite H3, AS_appsubst.
    all: try now rewrite H3, AS_substsubst.
    - now rewrite H1, AS_lamsubst.
    - inversion H0; subst.
      + now rewrite AS_idl.
      + now rewrite AS_snocomp, AS_0snoc.
      + now rewrite !AS_appsubst, !AS_substsubst.
      + rewrite !AS_lamsubst, !AS_substsubst.
        destruct (@confluencing_lift δ δ0) as [j [Hj1 Hj2]].
        now rewrite Hj1, Hj2.
      + now rewrite !AS_substsubst, !AS_ass. 
  Qed.
  Local Lemma confluencing_subst' {x δ' δ xδ}
  (H : TmASσstep' (x[δ']) xδ)
  (red_δ : δ' --s> δ)
  : confluencing TmASσstep xδ (x[δ]).
  Proof.
    inversion H; subst; inversion red_δ; subst; try solve_by_invert.
    all: try now rewrite H0, AS_appsubst.
    all: try now rewrite H0, AS_lamsubst.
    all: try now rewrite H0, AS_substsubst.
    - inversion H0.
      + now rewrite AS_subst_id.
      + reflexivity.
    - now rewrite AS_0snoc.
    - now rewrite H3, AS_0snoc.
  Qed.

End Lemmas.

Fixpoint TmsASσstepconfluenceAt (δ : TmsAS)
  : confluenceAt TmsASσstep TmsASσstep δ
with TmASσstepconfluenceAt (x : TmAS)
  : confluenceAt TmASσstep TmASσstep x.
Proof.
{ intros δ1 δ2 red1 red2.
    inversion red1;
      inversion red2.
  all: try solve_by_inverts 2.
  - apply (TmsASσstep'confluenceAt δ _ _ H H2).
  - subst; refine (confluencing_snoc H H2 ).
  - subst. refine (confluencing_snoc' H H2 ).
  - subst. refine (confluencing_comp H H2).
  - subst. refine (confluencing_comp' H H2).
  - subst; symmetry. refine (confluencing_snoc H2 H).
  - destruct δ; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmsASσstepconfluenceAt δ δ0 δ3 H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - subst; inversion H3; subst; now rewrite H, H2.
  - subst; symmetry; apply (confluencing_snoc' H2 H ).
  - subst; inversion H3; subst; now rewrite H, H2.
  - destruct δ; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmASσstepconfluenceAt a _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - subst; symmetry. refine (confluencing_comp H2 H).
  - destruct δ; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmsASσstepconfluenceAt δ4 _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - subst; inversion H3; subst; now rewrite H, H2. 
  - subst; symmetry; apply (confluencing_comp' H2 H).
  - subst; inversion H3; subst; now rewrite H, H2.
  - destruct δ; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmsASσstepconfluenceAt δ5 _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
}
{ intros a1 a2 red1 red2; inversion red1; inversion red2.
  all: try solve_by_inverts 2.
  - apply (TmASσstep'confluenceAt x a1 a2 H H2).
  - subst; apply (confluencing_subst H H2).
  - subst; apply (confluencing_subst' H H2).
  - subst; symmetry; apply (confluencing_subst H2 H).
  - destruct x; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmASσstepconfluenceAt x _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - subst; inversion H3; subst; now rewrite H, H2. 
  - subst; symmetry; apply (confluencing_subst' H2 H).
  - subst; inversion H3; subst; now rewrite H, H2.
  - destruct x; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmsASσstepconfluenceAt δ1 _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - destruct x; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmASσstepconfluenceAt x2 _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - subst; inversion H3; subst; now rewrite H, H2.
  - subst; inversion H3; subst; now rewrite H, H2.
  - destruct x; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmASσstepconfluenceAt x3 _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
  - destruct x; try discriminate; inversion H0; inversion H3; subst.
    destruct (TmASσstepconfluenceAt x _ _ H H2) as [j [Hj1 Hj2]].
    now rewrite Hj1, Hj2.
}
Qed.


Close Scope AS_scope.
