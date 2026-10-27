From Category Require Import Theory Lib.
From Category.Instance Require Import Sets.
From Category Require Import Theory.Morphisms.
From Category Require Import Tactics2.
From CwFdeBruijn Require Import CatPsh Uwcwf.

Open Scope morphism.

Definition ctl_c {C : UWCwF} (l:nat) := Nat.iter l s (⋆_ C).

Section π1id_epic.
  Context {C : UWCwF}.

  Lemma pi1_id_comp {m n:C} (δ : n ~{C}~> s m) : (π1 id{C}) ∘[C] δ ≈ π1 δ.
  Proof.
    rewrite pi1_comp, id_left.
    reflexivity.
  Qed.
  Lemma pi1_id_comp_snoc {m n:C} (δ : n ~{C}~> m) (a:Tm(n)) : (π1 id{C}) ∘[C] (⟨δ,a⟩) ≈ δ.
  Proof.
    rewrite pi1_comp, id_left.
    apply pi1_snoc.
  Qed.

  Lemma π1id_epic {m:C} (a : Tm m) : Epic (π1 id[s m]).
  Proof.
    constructor; intros n δ γ H.
    cat_simpl.
    rewrite <-(id_right δ), <-(id_right γ).
    rewrite <-(pi1_id_comp_snoc id a).
    rewrite !comp_assoc, H.
    cat_simpl.
  Qed.

  Lemma π1id_epic_ss {m:C} : Epic (π1 id[s (s m)]).
  Proof.
    apply (π1id_epic (π2 id)).
  Qed.
End π1id_epic.