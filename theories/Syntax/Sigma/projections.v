From CwFdeBruijn.Syntax.Sigma Require Import Sigma substid.
Require Import Setoid Morphisms RelationClasses.

Open Scope AS_scope.

Definition AS_pi1 (δ : TmsAS) := S ○ δ.
Definition AS_pi2 (δ : TmsAS) := 0[δ].

Global Instance AS_pi1_σstep_σconv : Proper (TmsASσstep ==> TmsASσconv) AS_pi1.
Proof. unfold AS_pi1; intros ? ? H; now rewrite H. Qed.
Global Instance AS_pi1_σconv : Proper (TmsASσconv ==> TmsASσconv) AS_pi1.
Proof. apply rt_lift_proper_1; apply _. Qed.
Global Instance AS_pi1_σstep_σeq : Proper (TmsASσstep ==> TmsASσeq) AS_pi1.
Proof. unfold AS_pi1; intros ? ? H; now rewrite H. Qed.
Global Instance AS_pi1_σeq : Proper (TmsASσeq ==> TmsASσeq) AS_pi1.
Proof. apply rst_lift_proper_1; apply _. Qed.

Global Instance AS_pi2_σstep_σconv : Proper (TmsASσstep ==> TmASσconv) AS_pi2.
Proof. unfold AS_pi2; intros ? ? H; now rewrite H. Qed.
Global Instance AS_pi2_σconv : Proper (TmsASσconv ==> TmASσconv) AS_pi2.
Proof. apply rt_lift_proper_1; apply _. Qed.
Global Instance AS_pi2_σstep_σeq : Proper (TmsASσstep ==> TmASσeq) AS_pi2.
Proof. unfold AS_pi2; intros ? ? H; now rewrite H. Qed.
Global Instance AS_pi2_σeq : Proper (TmsASσeq ==> TmASσeq) AS_pi2.
Proof. apply rst_lift_proper_1; apply _. Qed.

Lemma AS_pi1id : AS_pi1 id --s> S.
Proof.
  apply AS_srefl.
  apply AS_Sid.
Qed.

Lemma AS_pi1S : AS_pi1 S = S○S.
Proof. reflexivity. Qed.

Lemma AS_pi1snoc {δ a} : AS_pi1 <δ,a> --s> δ.
Proof.
  apply AS_srefl.
  apply AS_Ssnoc.
Qed.

Lemma AS_pi1comp {δ γ} :  (AS_pi1 δ) ○ γ --s> AS_pi1 δ○γ.
Proof.
  apply AS_srefl.
  apply AS_ass.
Qed.


Lemma AS_pi2id : AS_pi2 id --> 0.
Proof. 
  apply AS_refl.
  apply AS_0id.
Qed.

Lemma AS_pi2S : AS_pi2 S = 0[S].
Proof. reflexivity. Qed.

Lemma AS_pi2snoc {δ a} : AS_pi2 <δ,a> --> a.
Proof.
  apply AS_refl.
  apply AS_0snoc.
Qed.

Lemma AS_pi2comp {δ γ} : (AS_pi2 δ)[γ] --> AS_pi2 δ○γ .
Proof.
  apply AS_refl.
  apply AS_substsubst.
Qed.

Lemma AS_snoceta {δ} : < AS_pi1 δ , AS_pi2 δ> --s> δ .
Proof.
  apply AS_srefl.
  apply AS_eta.
Qed.

Close Scope AS_scope.