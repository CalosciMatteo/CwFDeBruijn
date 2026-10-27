From CwFdeBruijn.Syntax Require Import Setup
  Semantics.TypeCat
  Semantics.Monoid
  Semantics.Module.

Open Scope program_scope.
Open Scope typecat.
Open Scope nat.

Class KMM := {
  kmm_mnd : Monoid;
  kmm_mod :> Mod kmm_mnd;

  kiso : ModIsomorphism (MonoidMod kmm_mnd) (ProdMod (MonoidMod kmm_mnd) kmm_mod)
}.

Arguments kmm_mnd : clear implicits.
Arguments kiso : clear implicits.
Class KMMmorphism (H K : KMM) := {
  kmmor_mnd : MonoidMorphism (@kmm_mnd H) (@kmm_mnd K);
  kmmor_mod :> ModMorphism H (scalarRes kmmor_mnd K);
  
  kmmor_coherence : kmmor_mnd × kmmor_mod ∘ (kiso H) = (kiso K) ∘ kmmor_mnd 
}.

Lemma KMMmorphism_eq' {H K : KMM} {F G : KMMmorphism H K}
  (kmmor_mnd_eq : (@kmmor_mnd _ _ F) = (@kmmor_mnd _ _ G))
  : (@kmmor_mod _ _ F) = eq_rect_r
        (fun arg => ModMorphism H (scalarRes arg K))
        (@kmmor_mod _ _ G)
        kmmor_mnd_eq
  -> F = G.
Proof.
  intro kmmor_mod_eq.

  simple refine ( let H0 :
    (@modmor _ _ _
      (eq_rect_r
        (fun arg => ModMorphism H (scalarRes arg K))
        (@kmmor_mod _ _ G)
        kmmor_mnd_eq)
    = @modmor _ _ _ (@kmmor_mod _ _ G)) := _ in _).
    { rewrite kmmor_mnd_eq. reflexivity. }

  assert ( kmmor_coherence_eq :
    (@kmmor_coherence _ _ F
    = eq_rect_r
      (fun (arg : ModMorphism H (scalarRes kmmor_mnd K)) =>
        @mndmor _ _ (@kmmor_mnd _ _ F) × @modmor _ _ _ arg ∘ (kiso H) = (kiso K) ∘ @mndmor _ _  (@kmmor_mnd _ _ F))
      (eq_rect_r
        (fun arg => @mndmor _ _ (@kmmor_mnd _ _ F) × arg ∘ (kiso H) = (kiso K) ∘ @mndmor _ _  (@kmmor_mnd _ _ F))
        (eq_rect_r
          (fun arg =>
            @mndmor _ _ arg × @modmor _ _ _ (@kmmor_mod _ _ G) ∘ (kiso H) = (kiso K) ∘ @mndmor _ _  arg)
          (@kmmor_coherence _ _ G)
          kmmor_mnd_eq)
        H0)
      kmmor_mod_eq)).
  { apply proof_irrelevance. }

  destruct F, G.
  cbn in *.
  rewrite kmmor_coherence_eq, kmmor_mod_eq.
  destruct kmmor_mnd_eq.
  reflexivity.
Qed.

Lemma KMMmorphism_eq {H K : KMM} {F G : KMMmorphism H K}
  :  (@mndmor _ _ (@kmmor_mnd _ _ F) = @mndmor _ _ (@kmmor_mnd _ _ G))
  -> (@modmor _ _ _ (@kmmor_mod _ _ F) = (@modmor _ _ _ (@kmmor_mod _ _ G)))
  -> F = G.
Proof.
  intros kmmor_mnd_eq' kmmor_mod_eq'.
  destruct F as [[Fmnd ? ?] [Fmod ?] Fcoh], G as [[Gmnd ? ?] [Gmod ?] Gcoh].
  cbn in *.
  simple refine (KMMmorphism_eq' _ _).
  { cbn.
    apply MonoidMorphism_eq.
    cbn.
    exact kmmor_mnd_eq'. }
  apply ModMorphism_eq.
  destruct kmmor_mnd_eq'.
  destruct kmmor_mod_eq'.
  cbn.
  destruct ((proof_irrelevance _ _ _)).
  destruct ((proof_irrelevance _ _ _)).
  reflexivity.
Qed.

Section KMM.
  Context (H : KMM).

Definition kmm_id := @mnd_unit (kmm_mnd H) tt.

Definition kmm_id_cast : @mnd_unit (kmm_mnd H) = (@const _ unit kmm_id).
Proof.
  apply extensionality.
  induction x.
  reflexivity.
Qed.

Definition kmm_comp := (@mnd_op (kmm_mnd H)).

Lemma kmm_idl : kmm_comp ∘ (@const _ unit kmm_id) × id = snd.
Proof.
  rewrite <-kmm_id_cast.
  refine mnd_lunit.
Qed.

Lemma kmm_idr : kmm_comp ∘ id × (@const _ unit kmm_id) = fst.
Proof.
  rewrite <-kmm_id_cast.
  refine mnd_runit.
Qed.

Lemma kmm_ass
  : kmm_comp ∘ id × kmm_comp ∘ associator
  = kmm_comp ∘ kmm_comp × id.
Proof.
  unfold kmm_comp.
  refine mnd_ass.
Qed.

Lemma kmm_ass'
  : kmm_comp ∘ id × kmm_comp
  = kmm_comp ∘ kmm_comp × id ∘ associator_inv.
Proof.
  rewrite <-kmm_ass, <-comp_assoc.
  apply extensionality. intros [? []]. reflexivity.
Qed.

Definition kmm_pi1 : ModMorphism (MonoidMod (kmm_mnd H)) (MonoidMod (kmm_mnd H))
  := ModMor_compose (kiso H) Pi1ProdMod.

Definition kmm_pi1_lin
  : kmm_comp ∘ kmm_pi1 × id = kmm_pi1 ∘ kmm_comp
  := @modmor_lin _ _ _ kmm_pi1.

Lemma kmm_pi1id {A}
  : kmm_comp ∘ (@const _ A (kmm_pi1 kmm_id)) × id = kmm_pi1 ∘ snd.
Proof.
  eapply eq_trans with (kmm_comp ∘ (kmm_pi1 × id) ∘ (const kmm_id × id)).
  - apply extensionality. intros [? ?]. reflexivity.
  - rewrite kmm_pi1_lin.
    rewrite <-!comp_assoc.
    rewrite const_univ.
    rewrite bimap_compid.
    rewrite (comp_assoc (h:=kmm_comp)).
    rewrite kmm_idl.
    apply extensionality. intros [? ?]. reflexivity.
Qed.

Definition kmm_subst := (@mod_action (kmm_mnd H) H).

Lemma kmm_substsubst
  : kmm_subst ∘ kmm_subst × id = kmm_subst ∘ id × kmm_comp ∘ associator.
Proof.
  apply mod_ass.
Qed.

Lemma kmm_substid {A} : kmm_subst ∘ id × (@const _ A kmm_id) = fst.
Proof.
  rewrite const_univ, <-kmm_id_cast.
  rewrite bimap_idcomp, comp_assoc.
  eapply eq_trans.
  { 
    apply (f_equal (fun arg => arg ∘ id × const tt) ).
    apply mod_unitlaw. }
  apply extensionality; intros []; reflexivity.
Qed.

Definition kmm_pi2 : ModMorphism (MonoidMod (kmm_mnd H)) H
:= ModMor_compose (kiso H) Pi2ProdMod.

Definition kmm_pi2_lin
  : kmm_subst ∘ kmm_pi2 × id = kmm_pi2 ∘ kmm_comp
  := @modmor_lin _ _ _ kmm_pi2.

Lemma kmm_pi2id {A}
  : kmm_subst ∘ (@const _ A (kmm_pi2 kmm_id)) × id = kmm_pi2 ∘ snd.
Proof.
  eapply eq_trans with (kmm_subst ∘ (kmm_pi2 × id) ∘ (const kmm_id × id)).
  - apply extensionality. intros [? ?]. reflexivity.
  - rewrite kmm_pi2_lin.
    rewrite <-!comp_assoc.
    rewrite const_univ.
    rewrite bimap_compid.
    rewrite (comp_assoc (h:=kmm_comp)).
    rewrite kmm_idl.
    apply extensionality. intros [? ?]. reflexivity.
Qed.

Definition kmm_snoc := ModInvMorphism (kiso H).

(* Lemma kmm_snoc_lin : kmm_comp ∘ kmm_snoc × id = kmm_snoc *)

Lemma kmm_snoc_invkiso : inv (kiso H) = kmm_snoc.
Proof.
  reflexivity.
Qed.

Lemma kmm_pi2snoc : kmm_pi2 ∘ kmm_snoc = snd.
Proof.
  apply (compiso_r (kiso H)).
  rewrite <-comp_assoc, <-kmm_snoc_invkiso.
  rewrite (inv_l (iso := kiso H)).
  reflexivity.
Qed.

Lemma kmm_pi1snoc : kmm_pi1 ∘ kmm_snoc = fst.
Proof.
  apply (compiso_r (kiso H)).
  rewrite <-comp_assoc, <-kmm_snoc_invkiso.
  rewrite (inv_l (iso := kiso H)).
  reflexivity.
Qed.

Lemma kmm_snoc_eta : kmm_snoc ∘ kmm_pi1 × kmm_pi2 ∘ diag = id.
Proof.
  apply (compiso_l (kiso H)).
  rewrite !comp_assoc, <-kmm_snoc_invkiso.
  rewrite (inv_r (iso := kiso H)).
  apply uniqmap_prod;
    apply extensionality; intro; reflexivity.
Qed.

(*Linearity of snoc*)
Lemma kmm_snocomp : kmm_comp ∘ kmm_snoc × id = kmm_snoc ∘ (kmm_comp)×(kmm_subst) ∘ doppel.
Proof.
  rewrite <-!comp_assoc.
  change (kmm_comp × kmm_subst ∘ doppel) with (@mod_action _ (ProdMod (MonoidMod (kmm_mnd H)) kmm_mod)).
  change kmm_comp with (@mod_action _ (MonoidMod (kmm_mnd H))).
  apply (@modmor_lin _ _ _ kmm_snoc).
Qed.

Lemma kmm_snocomp'' {A} {f δ: A -> kmm_mnd H} {t : A -> H}
: kmm_comp ∘ (kmm_snoc ∘ δ × t) × f = kmm_snoc ∘ (kmm_comp ∘ δ × f )×(kmm_subst ∘ t × f) ∘ doppel.
Proof.
  eapply eq_trans with (kmm_comp ∘ kmm_snoc × id ∘ (δ × t) × f).
  { apply extensionality. intros [[? ?] ?]. reflexivity. }
  rewrite kmm_snocomp.
  apply extensionality. intros [[? ?] ?]. reflexivity.
Qed.

Definition kmm_deriv : (kmm_mnd H) -> (kmm_mnd H)
  := kmm_snoc ∘ (kmm_comp ∘ (id × (const (kmm_pi1 kmm_id))) ∘ diag) × (const (kmm_pi2 kmm_id)) ∘ diag.

Lemma kmm_pi2deriv : kmm_pi2 ∘ kmm_deriv = const (kmm_pi2 kmm_id).
Proof.
  unfold kmm_deriv.
  rewrite !comp_assoc.
  rewrite kmm_pi2snoc.
  apply extensionality. intros. reflexivity.
Qed.

Lemma kmm_pi1deriv
  : kmm_pi1 ∘ kmm_deriv = 
  kmm_comp ∘ (id × const (kmm_pi1 kmm_id)) ∘ diag.
Proof.
  unfold kmm_deriv.
  rewrite !comp_assoc.
  rewrite kmm_pi1snoc.
  apply extensionality. intros. reflexivity.
Qed.

Lemma kmm_derivcomp
  : kmm_comp ∘ (kmm_deriv × id)
  = kmm_snoc ∘ (kmm_comp ∘ (id × kmm_pi1)) × (kmm_pi2) ∘ associator_inv ∘ id × diag.
Proof.
  unfold kmm_deriv.
  rewrite compdiagtimes, !comp_assoc.
  rewrite kmm_snocomp''.
  f_equal.
  rewrite <-!comp_assoc, bimap_compid.
  rewrite !comp_assoc, <-kmm_ass, compdiagtimes,
   <-!comp_assoc, (comp_assoc (h:=associator)), associator_bimap, !comp_assoc.
  (* rewrite !comp_assoc -kmm_ass compdiagtimes !-comp_assoc (comp_assoc (h:=associator)) associator_bimap !comp_assoc. *)
  rewrite <-!comp_assoc, (comp_assoc(h:= id × kmm_comp)), <-bimap_idcomp.
  rewrite kmm_pi1id.
  rewrite kmm_pi2id.
  apply extensionality; intros [? ?]; reflexivity.
Qed.

Program Definition DerivMonoidMor
: MonoidMorphism (kmm_mnd H) (kmm_mnd H) := {|
  mndmor := kmm_deriv
|}.
Next Obligation.
  change mnd_op with kmm_comp.
  rewrite bimap_id, comp_assoc.
  rewrite kmm_derivcomp.
  unfold kmm_deriv at 2.
  rewrite <-!comp_assoc.
  f_equal.
  rewrite <-bimap_idcomp.
  rewrite diagcomp. 
  rewrite bimap_idcomp.
  rewrite (comp_assoc (h:=associator_inv)), associator_inv_bimap.
  rewrite !comp_assoc.
  rewrite (bimap_comp _ _ (kmm_comp ∘ id × kmm_pi1) kmm_pi2).
  rewrite kmm_pi2deriv.
  rewrite <-(comp_assoc (h:= kmm_comp)), <-bimap_idcomp.
  eapply eq_trans.
  { 
    apply (f_equal (fun x =>
      (kmm_comp ∘ id × x) × const (kmm_pi2 kmm_id)
      ∘ associator_inv
      ∘ id × diag)).
    apply kmm_pi1deriv.
  }
  rewrite !compdiagtimes'.
  rewrite <-(comp_assoc(h:=kmm_comp)), bimap_idcomp,  !comp_assoc.
  rewrite kmm_ass'.
  apply extensionality. intros []. reflexivity.
Qed.

Next Obligation.
  rewrite kmm_id_cast.
  unfold kmm_deriv.

  apply (compiso_l (kiso H)).
  rewrite !comp_assoc, <-kmm_snoc_invkiso, (inv_r(iso := (kiso H))).

  apply uniqmap_prod; [rewrite <-kmm_pi1snoc at 2 | rewrite <-kmm_pi2snoc at 2].
  all: rewrite <-!comp_assoc, (comp_assoc(h:=kmm_snoc)).
  all: rewrite <-kmm_snoc_invkiso, (inv_l(iso := (kiso H))).
  2:{ apply extensionality. intros []. reflexivity. }
  (* rewrite const_univ, (comp_assoc (h:= id)), (comp_assoc (h:= kmm_comp)). *)
  rewrite compose_id_left, !comp_assoc, fst_beta, !compdiagtimes.
  rewrite <-!comp_assoc, diagcomp, compose_id_left.
  eapply eq_trans with (kmm_comp ∘ id × const (kmm_pi1 kmm_id) ∘ diag ∘ const kmm_id).
  { apply extensionality. intros []. reflexivity. }

  rewrite <-!comp_assoc, diagcomp, (comp_assoc (h:= id × const _)).
  rewrite bimap_comp, compose_id_left.
  rewrite bimap_id, !comp_assoc.
  rewrite kmm_idl.
  apply extensionality. intros []. reflexivity.
Qed.

Lemma kmm_compderiv : kmm_comp ∘ kmm_deriv × kmm_deriv = kmm_deriv ∘ kmm_comp.
Proof.
refine (@mndmor_op _ _ DerivMonoidMor). 
Qed.

Lemma kmm_derivid : kmm_deriv ∘ (@const _ unit kmm_id) = (@const _ unit kmm_id).
Proof.
rewrite <-kmm_id_cast.
refine (@mndmor_unit _ _ DerivMonoidMor). 
Qed.

Program Instance DerivMod : Mod (kmm_mnd H) :={|
  mod_obj := kmm_mod;
  mod_action := kmm_subst ∘ (id × kmm_deriv)
|}.
Next Obligation.
  change mnd_op with kmm_comp.
  eapply eq_trans with (kmm_subst ∘ kmm_subst × id ∘ (id × kmm_deriv) × kmm_deriv).
  { apply extensionality. intros [[? ?] ?]. reflexivity. }
  rewrite kmm_substsubst.
  rewrite <-!comp_assoc; f_equal.

  rewrite associator_bimap, comp_assoc, <-bimap_idcomp.
  rewrite kmm_compderiv.
  rewrite bimap_idcomp.
  reflexivity.
Qed.

Next Obligation.
  rewrite kmm_id_cast.
  unfold runitor.
  rewrite <-comp_assoc, <-bimap_idcomp.
  rewrite kmm_derivid.
  apply kmm_substid.
Qed.

End KMM.

Class KMMλappmodel := {
  KMMλappmodel_kmm :> KMM;
  kmm_app : ModMorphism
    (ProdMod KMMλappmodel_kmm KMMλappmodel_kmm)
    KMMλappmodel_kmm;

  kmm_lam : ModMorphism
  (DerivMod KMMλappmodel_kmm)
  KMMλappmodel_kmm;
}.

Section KMMλappmodel.
  Context (H : KMMλappmodel).

  Lemma kmm_substlam
  : (kmm_subst H) ∘ kmm_lam × id = kmm_lam ∘ ((kmm_subst H) ∘ id × (kmm_deriv H)).
  Proof.
    refine (@modmor_lin _ _ _ kmm_lam).
  Qed.

  Lemma kmm_substlam' {A B} {t : A -> H} {δ : B -> (kmm_mnd H)}
  : (kmm_subst H) ∘ ((kmm_lam × id ) ∘ t × δ) = kmm_lam ∘ ((kmm_subst H) ∘ t × ((kmm_deriv H) ∘ δ)).
  Proof.
    eapply eq_trans.
    { rewrite comp_assoc.
      rewrite kmm_substlam.
      reflexivity. }
    apply extensionality. intros []. reflexivity.
  Qed.

  Lemma kmm_substapp
  : (kmm_subst H) ∘ kmm_app × id = kmm_app ∘ ((kmm_subst H) × (kmm_subst H) ∘ doppel).
  Proof.
    refine (@modmor_lin _ _ _ kmm_app).
  Qed.

End KMMλappmodel.

Lemma kmmor_coherence_pi1 {H K} (F : KMMmorphism H K)
  : kmmor_mnd ∘ (kmm_pi1 H) 
  = (kmm_pi1 K) ∘ kmmor_mnd.
Proof.
  unfold kmm_pi1.
  cbn.
  rewrite <-comp_assoc.
  rewrite <-(kmmor_coherence(K:=K)).
  rewrite !comp_assoc.
  f_equal.
  apply extensionality. intros []. reflexivity.
Qed.

Lemma kmmor_coherence_pi2 {H K} (F : KMMmorphism H K)
  : F ∘ (kmm_pi2 H) 
  = (kmm_pi2 K) ∘ kmmor_mnd.
Proof.
  unfold kmm_pi2.
  cbn.
  rewrite <-comp_assoc.
  rewrite <-(kmmor_coherence(K:=K)).
  rewrite !comp_assoc.
  f_equal.
  apply extensionality. intros []. reflexivity.
Qed.

Lemma kmmor_coherence_snoc {H K} (F : KMMmorphism H K)
  : (@kmmor_mnd _ _ F) ∘ (kmm_snoc H) 
  = (kmm_snoc K) ∘ (@kmmor_mnd _ _ F) × kmmor_mod.
Proof.
  refine (proj2 (compiso_r (@modiso_is _ _ _ (kiso H))) _).
  rewrite <-!comp_assoc.
  rewrite <-kmm_snoc_invkiso.
  rewrite inv_l.

  symmetry.

  eapply eq_trans.
  { apply (f_equal (fun arg => kmm_snoc K ∘ arg)).
    apply (kmmor_coherence (KMMmorphism := F)). }
  
  rewrite comp_assoc.
  rewrite <-kmm_snoc_invkiso.
  rewrite inv_l.
  reflexivity.
Qed.

Class KMMλappMorphism (H K : KMMλappmodel) := {
  KMMλapp_kmmmor :> KMMmorphism H K;
  KMMλapp_appcoh
    : KMMλapp_kmmmor ∘ kmm_app
    = kmm_app ∘ KMMλapp_kmmmor × KMMλapp_kmmmor;
  KMMλapp_lamcoh
    : KMMλapp_kmmmor ∘ kmm_lam
    = kmm_lam ∘ KMMλapp_kmmmor
}.

Lemma KMMλappMorphism_eq {H K : KMMλappmodel}
  {F G : KMMλappMorphism H K}
  : ((@KMMλapp_kmmmor _ _ F) = (@KMMλapp_kmmmor _ _ G)) -> F = G.
Proof.
  intro KMMλapp_kmmmor_eq.

  assert ( KMMλapp_appcoh_eq
    : @KMMλapp_appcoh _ _ F
    = eq_rec_r
        (fun arg => (@kmmor_mod _ _ arg) ∘ kmm_app = kmm_app ∘ (@kmmor_mod _ _ arg) × (@kmmor_mod _ _ arg))
        (@KMMλapp_appcoh _ _ G)
        KMMλapp_kmmmor_eq).
  { apply proof_irrelevance. }

  assert ( KMMλapp_lamcoh
  : @KMMλapp_lamcoh _ _ F
  = eq_rec_r
      (fun arg => (@kmmor_mod _ _ arg) ∘ kmm_lam
      = kmm_lam ∘ (@kmmor_mod _ _ arg) )
      (@KMMλapp_lamcoh _ _ G)
      KMMλapp_kmmmor_eq).
  { apply proof_irrelevance. }
  destruct F, G.
  cbn in *.
  rewrite KMMλapp_lamcoh, KMMλapp_appcoh_eq, KMMλapp_kmmmor_eq.
  reflexivity.
Qed.