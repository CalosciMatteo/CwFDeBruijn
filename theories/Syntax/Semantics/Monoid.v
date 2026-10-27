Require Import Stdlib.Logic.ProofIrrelevance.
From CwFdeBruijn.Syntax Require Export Semantics.TypeCat.

Open Scope program_scope.
Open Scope typecat.

Class Monoid := {
  mnd_obj : Type;
  mnd_unit : unit -> mnd_obj;
  mnd_op : mnd_obj * mnd_obj -> mnd_obj;

  mnd_ass
    : mnd_op ∘ id × mnd_op ∘ associator
    = mnd_op ∘ mnd_op × id;

  mnd_lunit
    : mnd_op ∘ mnd_unit × id = lunitor;

  mnd_runit
    : mnd_op ∘ id × mnd_unit = runitor
}.

Coercion mnd_obj : Monoid >-> Sortclass.

Class MonoidMorphism (M N : Monoid) := {
  mndmor :> M -> N;

  mndmor_op : mnd_op ∘ mndmor × mndmor = mndmor ∘ mnd_op;
  mndmor_unit : mndmor ∘ mnd_unit = mnd_unit
}.

Lemma MonoidMorphism_eq {M N : Monoid} {F G : MonoidMorphism M N}
  : ((@mndmor _ _ F) = (@mndmor _ _ G)) -> F = G.
Proof.
  intro mndmor_eq.
  assert (mndmor_op_eq
    : @mndmor_op _ _ F
    = eq_rec_r
        (fun arg => mnd_op ∘ arg × arg = arg ∘ mnd_op)
        (@mndmor_op _ _ G)
        mndmor_eq).
  { apply proof_irrelevance. }
  assert (mndmor_unit_eq
    : @mndmor_unit _ _ F
    = eq_rec_r
        (fun arg => arg ∘ mnd_unit = mnd_unit)
        (@mndmor_unit _ _ G)
        mndmor_eq).
  { apply proof_irrelevance. }
  destruct F, G.
  cbn in *.
  rewrite mndmor_unit_eq, mndmor_op_eq, mndmor_eq.
  reflexivity.
Defined.