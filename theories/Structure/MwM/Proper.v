From Stdlib Require Import ssrfun Nat PeanoNat Lia.
From Category Require Import Lib Theory.

From Category Require Import Instance.Sets.
From Category Require Import Construction.Subcategory.
From CwFdeBruijn Require Import Lib.Iter CatPsh Uwcwf Structure.Uwcwf FullSubCategory MwM.

Section definitions.

  Context {M : MwM}.

  (* Proper specification: the term set is not a singleton *)
  Class NonSingleton : Type := {
    nsingl_aTerm : @MwM_T M;
    nsingl_neq : ¬ (nsingl_aTerm ≈ MwM_pi2 id);
  }.

End definitions.

Definition MwMns := { M : MwM & @NonSingleton M }.
Definition MwMns_incl : MwMns -> MwM
  := @projT1 MwM (@NonSingleton).
Coercion MwMns_incl : MwMns >-> MwM.
Instance MwMns_NonSingleton (M : MwMns) : @NonSingleton M
  := projT2 M.

Open Scope nat.
Lemma uniqueness_lifted_id {M : MwMns} (i j : nat)
  (E: iter i MwM_pi1 id{M} ≈ iter j MwM_pi1 id)
  : i=j.
Proof.
  assert (ProofWithWlog : forall i j
    (E : iter i MwM_pi1 id{M} ≈ iter j MwM_pi1 id{M}),
    i <= j -> i = j).
  2: { 
    assert (Hdec : i <= j \/ j <= i) by lia.
    destruct Hdec as [Hle | Hge]; [|symmetry; symmetry in E];
    apply ProofWithWlog; assumption.
  }
  clear i j E; intros i j E le.
  set (d := j-i).
  assert (E_d : j = i + d) by lia.
  rewrite E_d in *.
  assert (H : iter d MwM_pi1 id ≈ id{M}).
  { symmetry.
    apply (MwM_iterpi1id_epic i).
    rewrite MwM_iterpi1_id_comp.
    rewrite <-Nat.iter_add, Nat.add_comm.
    cat. }
  clear E le E_d.
  destruct d; [lia|exfalso].
  clear i j.
  set (σ := (iter (S d) (MwM_snoc^~ nsingl_aTerm) id{M})).

  apply nsingl_neq.
  unshelve etransitivity; [exact (MwM_pi2 (id ∘ σ)) | |].
  { rewrite id_left.
    unfold σ.
    simpl.
    rewrite MwM_pi2_snoc.
    reflexivity.
  }
  etransitivity; [now rewrite <-H |].
  unfold σ.
  clear σ.
  clear H.
  rewrite MwM_iterpi1_id_comp.

  assert (E: forall d0, 
    iter (S d0) MwM_pi1
      (iter (S d0) (MwM_snoc^~ nsingl_aTerm) id{M})
    ≈
    id
    ).
  { clear d; induction d0 as [|d IHd].
  - simpl.
    rewrite MwM_pi1_snoc.
    reflexivity.
  - rewrite (Nat.iter_succ _ _ MwM_pi1).
    rewrite <-(Nat.iter_swap _ _ MwM_pi1).
    rewrite (Nat.iter_succ _ _ (MwM_snoc^~ nsingl_aTerm)).
    rewrite MwM_pi1_snoc.
    rewrite IHd.
    reflexivity.
  }
  rewrite E.
  reflexivity.
Qed.

Lemma uniqueness_refs {M : MwMns} (i j : nat)
  (E: MwM_pi2 (iter i MwM_pi1 id{M}) ≈ MwM_pi2 (iter j MwM_pi1 id))
  : i=j.
Proof.
  assert (ProofWithWlog : forall i j
    (E  : MwM_pi2 (iter i MwM_pi1 id{M})
        ≈ MwM_pi2 (iter j MwM_pi1 id)),
    i <= j -> i = j).
  2: { 
    assert (Hdec : i <= j \/ j <= i) by lia.
    destruct Hdec as [Hle | Hge]; [|symmetry; symmetry in E];
    apply ProofWithWlog; assumption.
  }
  clear i j E; intros i j E le.
  set (d := j-i).
  assert (E_d : j = i + d) by lia.
  rewrite E_d in *.
  destruct d; [lia|exfalso].
  clear j E_d le.

  set (σ' := (iter d (MwM_snoc^~ (MwM_pi2 id{M})) id{M})).
  set (σ := (iter (S i) (MwM_snoc^~ nsingl_aTerm) σ')).

  apply nsingl_neq.

  etransitivity;[etransitivity|]. 
  2: refine (proper_MwM_subst _ _ E σ σ _); reflexivity.
  - unfold σ, σ'.
    rewrite MwM_pi2_subst, MwM_iterpi1_id_comp.
    rewrite Nat.iter_succ_r, MwM_iterpi1_itersnoc.
    rewrite MwM_pi2_snoc.
    reflexivity.
  - 
    assert (H:i + S d = d + S i) by lia.
    rewrite H.

    unfold σ, σ'.
    rewrite MwM_pi2_subst, MwM_iterpi1_id_comp.
    rewrite Nat.iter_add, MwM_iterpi1_itersnoc, MwM_iterpi1_itersnoc.
    reflexivity.
Qed.
Close Scope nat.