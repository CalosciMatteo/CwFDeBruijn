From CwFdeBruijn.Syntax Require Import Setup Semantics.Monoid Semantics.TypeCat.

Open Scope program_scope.
Open Scope typecat.

Arguments inv {_ _ _} _.

Class Mod (mon : Monoid) := {
  mod_obj : Type;
  mod_action : mod_obj * mon -> mod_obj;

  mod_ass
    : mod_action ∘ mod_action × id 
    = mod_action ∘ id × mnd_op ∘ associator;

  mod_unitlaw
    : mod_action ∘ id × mnd_unit = runitor
}.

Coercion mod_obj : Mod >-> Sortclass.

Class ModMorphism {mon : Monoid} (M N : Mod mon) := {
  modmor :> M -> N;

  modmor_lin : mod_action ∘  modmor × id = modmor ∘ mod_action
}.

Lemma ModMorphism_eq {mon : Monoid} {M N : Mod mon}
  {F G : ModMorphism M N}
  : ((@modmor _ _ _ F) = (@modmor _ _ _ G)) -> F = G.
Proof.
  intro modmor_eq.
  assert ( modmor_lin_eq
    : @modmor_lin _ _ _ F
    = eq_rec_r
        (fun arg => mod_action ∘  arg × id = arg ∘ mod_action)
        (@modmor_lin _ _ _ G)
        modmor_eq).
  { apply proof_irrelevance. }
  destruct F, G.
  cbn in *.
  rewrite modmor_lin_eq, modmor_eq.
  reflexivity.
Qed.

Program Definition ModMor_compose {mon : Monoid} {M N P: Mod mon}
  (f : ModMorphism M N) (g : ModMorphism N P)
  : ModMorphism M P := {|
    modmor := g ∘ f
  |}.
Next Obligation.
rewrite <-comp_id, <-bimap_comp, comp_assoc.
rewrite !modmor_lin, <-comp_assoc, modmor_lin.
reflexivity.
Qed.
Class ModIsomorphism {mon : Monoid} (M N : Mod mon) := {
  modiso : ModMorphism M N;

  modiso_is : iso modmor 
}.

Coercion modiso : ModIsomorphism >-> ModMorphism.
Coercion modiso_is : ModIsomorphism >-> iso.

Program Definition ModInvMorphism {mon} {M N : Mod mon} (f : ModIsomorphism M N)
  : ModIsomorphism N M := {|
  modiso := {| 
    modmor := inv modiso_is;
    modmor_lin := _
  |};
  modiso_is := _
|}.

Next Obligation.
  apply (compiso_l modiso_is).
  rewrite !comp_assoc.
  rewrite <-modmor_lin.
  rewrite <-comp_assoc.
  rewrite bimap_comp.
  rewrite inv_r.
  rewrite bimap_ofid.
  reflexivity.
Qed.
Next Obligation.
  eapply Build_iso with f.
  - apply inv_l.
  - apply inv_r.
Qed.

(* A monoid is a module over itself*)
Program Instance MonoidMod (mon : Monoid) : Mod mon :={|
  mod_obj := mon;
  mod_action := mnd_op
|}.
Next Obligation.
  symmetry.
  apply mnd_ass.
Qed.
Next Obligation.
  apply mnd_runit.
Qed.

(* Product of modules is a module *)
Program Instance ProdMod {mon : Monoid} (M N : Mod mon): Mod mon :={|
  mod_obj := M*N;
  mod_action := bimap mod_action mod_action ∘ doppel
|}.
Next Obligation.
  apply uniqmap_prod.
  - apply extensionality.
    intros [[[m n] x] y].
    cbn.
    exact (equal_f mod_ass (m,x,y)).
  - apply extensionality.
    intros [[[m n] x] y].
    cbn.
    exact (equal_f mod_ass (n,x,y)).
Qed.
Next Obligation.
  apply uniqmap_prod.
  - apply extensionality.
    intros [[m n] tt].
    cbn.
    exact (equal_f mod_unitlaw (m,tt)).
  - apply extensionality.
    intros [[m n] tt].
    cbn.
    exact (equal_f mod_unitlaw (n,tt)).
Qed.

(* Projection morphisms *)
Program Instance Pi1ProdMod {mon : Monoid} {M N : Mod mon} : ModMorphism (ProdMod M N) M :={|
  modmor := fst;
|}.
Next Obligation.
  apply extensionality.
  intros [[m n] x].
  reflexivity.
Qed.

Program Instance Pi2ProdMod {mon : Monoid} {M N : Mod mon} : ModMorphism (ProdMod M N) N :={|
  modmor := snd;
|}.
Next Obligation.
  apply extensionality. 
  intros [[m n] x].
  reflexivity.
Qed.

(* restriction of Scalar *)
Program Instance scalarRes {X Y : Monoid} (f : MonoidMorphism X Y) (M : Mod Y) : Mod X :={|
  mod_obj := M;
  mod_action := mod_action ∘ id × f;
|}.
Next Obligation.
  apply extensionality.
  intros [[m x] x'].
  unfold compose, id.
  cbn.
  eapply eq_trans.
  { exact (equal_f mod_ass (m, f x, f x')). }
  unfold compose, id.
  cbn.
  repeat f_equal.
  apply (equal_f mndmor_op (x,x')).
Qed.
Next Obligation.
  apply extensionality.
  intros [m tt].
  unfold compose, id.
  cbn.
  rewrite ((equal_f mndmor_unit tt) : f _ = _).
  apply ((equal_f mod_unitlaw (m,tt))).
Qed.