From CwFdeBruijn.Syntax.dB Require Import dB substLemmas.

Declare Scope dB_scope.
Delimit Scope dB_scope with dB.
Open Scope dB_scope.

Notation "'id'" := dB_ref (at level 5). 
Notation "δ '○' γ" := (assign_comp δ γ) (at level 9) : dB_scope.
Notation "'⟨' δ ',' a '⟩'" := (dB_snoc δ a) (δ at level 40, a at level 40) : dB_scope.
Notation "a '@' b" := (dB_app a b) (at level 9)  : dB_scope.
Notation "a '[' δ ']'" := (dB_subst δ a) (at level 9, δ at level 200)  : dB_scope.
Notation "'λ' a" := (dB_lam a) (at level 40)  : dB_scope.
Notation "'π1' δ" := (assign_π₁ δ) (at level 40)  : dB_scope.
Notation "'π2' δ" := (δ 0) (at level 40)  : dB_scope.
(* data for dB as a MwM *)
Section dBasMwM.
(* S is a monoid *)
Lemma dB_idl {δ} : id ○ δ = δ.
Proof.
  reflexivity.
Qed.
Lemma dB_idr {δ} : id ○ δ = δ.
Proof.
  reflexivity.
Qed.
Lemma dB_ass {δ1 δ2 δ3} : (δ1 ○ δ2) ○ δ3 = δ1 ○ (δ2 ○ δ3).
Proof.
  apply extensionality; intro n.
  apply dB_subst_subst.
Qed.
(* T is module *)

(* Context Comprehension *)
Lemma db_pi1snoc {δ a} : π1 ⟨δ,a⟩ = δ.
Proof. reflexivity. Qed.
Lemma db_pi2snoc {δ a} : π2 ⟨δ,a⟩ = a. 
Proof. reflexivity. Qed.
Lemma dB_snoc_eta δ : ⟨ π1 δ , π2 δ⟩ = δ.
Proof. apply extensionality. intros [|i]; reflexivity. Qed.
Lemma db_pi1comp {δ γ} : π1 (δ ○ γ) = (π1 δ) ○ γ.
Proof. reflexivity. Qed.
Lemma db_pi2comp {δ γ} : π2 (δ ○ γ) = (π2 δ)[γ].
Proof. reflexivity. Qed.
Lemma db_snocomp {δ γ a} : ⟨δ,a⟩○γ = ⟨δ○γ,a[γ]⟩.
Proof. apply extensionality; intros [|i]; reflexivity. Qed.

End dBasMwM.

Close Scope dB_scope.