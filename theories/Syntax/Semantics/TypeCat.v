From CwFdeBruijn.Syntax Require Import Setup.
From Stdlib Require Export Program.Basics.

Declare Scope typecat.

Open Scope type.
Open Scope typecat.
Open Scope program_scope.

Lemma comp_assoc {A B C D} {f:A->B} {g:B->C} {h:C->D} : h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof.
  reflexivity.
Defined.

(*Monoidal structure of Type*)

Definition associator {A B C} : (A * B) * C -> A * (B * C).
Proof.
  intros [[a b] c].
  exact (a,(b,c)).
Defined.

Definition associator_inv {A B C} : A * (B * C) -> (A * B) * C.
Proof.
  intros [a [b c]].
  exact ((a,b),c).
Defined.

Definition lunitor {A} : (unit * A) -> A := snd.
Definition runitor {A} : (A * unit) -> A := fst.

Definition bimap {A' B' A B} (f:A'->A) (g:B'->B)
  : A' * B' -> A * B.
Proof.
  intros [a b].
  exact (f a,g b).
Defined.

Notation "f × g" := (bimap f g) (at level 30) : typecat.

Lemma associator_bimap {A' A B' B C' C} {f : A'-> A} {g : B' -> B} {h : C' -> C}
  : associator ∘ ((f × g) × h)  = (f × (g × h)) ∘ associator.
Proof.
  apply extensionality.
  intros [[a b] c].
  reflexivity.
Defined.

Lemma associator_inv_bimap {A' A B' B C' C} {f : A'-> A} {g : B' -> B} {h : C' -> C}
  : associator_inv ∘ (f × (g × h)) = ((f × g) × h) ∘ associator_inv.
Proof.
  apply extensionality.
  intros [a [b c]].
  reflexivity.
Defined.

Lemma snd_beta {A' B' A B} (f:A'->A) (g:B'->B) : snd ∘ (f × g) = snd ∘ id × g.
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma fst_beta {A' B' A B} (f:A'->A) (g:B'->B) : fst ∘ (f × g) = fst ∘ f × id.
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma bimap_comp {A'' B'' A' B' A B} (f':A''->A') (g':B''->B') (f:A'->A) (g:B'->B)
  : f × g ∘ f' × g' = (f∘f')× (g ∘ g').
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma bimap_id {A' B' A B} (f:A'->A) (g:B'->B)
  : f × g = (f×id)∘ (id × g).
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma bimap_compid {A B C D} (f:A->B) (g:B->C)
  : (g∘f) × (@id D) = (g×id)∘ (f × id).
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma bimap_idcomp {A B C D} (f:A->B) (g:B->C)
  : (@id D) × (g∘f) = (id×g) ∘ (id × f).
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma bimap_ofid {A B}
  : id × id = (@id (A*B)).
Proof.
  apply extensionality.
  intros [a b].
  reflexivity.
Qed.

Lemma const_univ {A B} {b:B} : @const _ A b = (@const _ unit b) ∘ (@const _ A tt).
Proof.
  apply extensionality.
  reflexivity.
Qed.

Lemma comp_id {A}
  : id ∘ id = (@id A).
Proof.
  apply extensionality.
  reflexivity.
Qed.

Definition doppel {A B C} : (A * B) * C -> (A * C) * (B * C).
Proof.
  intros [[a b] c].
  exact ((a,c),(b,c)).
Defined.

Lemma doppel_bimap { A' A B' B C C'} (f: A'*C -> A) (g: B'*C -> B) (h: C' -> C)
  : f × g ∘ doppel ∘ id × h
  = (f ∘ id × h) × (g ∘ id × h) ∘ doppel.
Proof.
  apply extensionality.
  intros [[? ?] ?].
  reflexivity.
Qed. 

Definition uniqmap_prod {A B C} {f g : A -> B*C}
  (e_fst : fst ∘ f = fst ∘ g)
  (e_snd : snd ∘ f = snd ∘ g)
  : f = g.
Proof.
  apply extensionality.
  intro a.
  specialize (equal_f e_fst a).
  specialize (equal_f e_snd a).
  unfold compose.
  destruct (f a).
  destruct (g a).
  cbn.
  intros e e'.
  destruct e.
  destruct e'.
  reflexivity.
Qed.

Definition diag {A} : A -> A * A := fun a => (a,a).

Lemma diagcomp A B (f: A -> B) : diag ∘ f = f × f ∘ diag.
Proof.
  apply extensionality. intros. reflexivity.
Qed.

Lemma compdiagtimes A B C (h: A*A ->B) : (h ∘ diag) × (@id C) = h × id ∘ diag × id.
Proof.
  apply extensionality. intros [? ?]. reflexivity.
Qed.

Lemma compdiagtimes' {A B C' C} (h: A*A ->B) (f:C' -> C) : (h ∘ diag) × (f) = h × id ∘ diag × f.
Proof.
  apply extensionality. intros [? ?]. reflexivity.
Qed.

(*isomorphism of Type*)

Class iso {A B} (f : A -> B) := {
  inv : B -> A;
  inv_r : f ∘ inv = id;
  inv_l : inv ∘ f = id;
}.

Lemma compiso_r {A B C} {g h : B -> C} {f:A -> B} (is : iso f)
  : g = h <-> g ∘ f = h ∘ f.
Proof.
  split.
  - intro e. destruct e. reflexivity.
  - intro e.
    change (g ∘ id = h ∘ id).
    rewrite <-(inv_r).
    rewrite !comp_assoc.
    rewrite e.
    reflexivity.
Qed.

Lemma compiso_l {A B C} {g h : A -> B} {f:B -> C} (is : iso f)
  : g = h <-> f ∘ g = f ∘ h.
Proof.
  split.
  - intro e. destruct e. reflexivity.
  - intro e.
    change (id ∘ g = id ∘ h).
    rewrite <-(inv_l (iso := is)).
    rewrite <-!comp_assoc.
    rewrite e.
    reflexivity.
Qed.