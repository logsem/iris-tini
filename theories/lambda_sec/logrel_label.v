From iris.algebra Require Import list.
From logrel_ifc.lambda_sec Require Export lattice typing.

Canonical Structure labelO `{SecurityLattice l} := leibnizO l.

Section logrel.
  Context `{!SecurityLattice label}.

  Implicit Types ρ : listO labelO.
  Implicit Types ℓ : labelO.
  Implicit Types l : label_term.

  Fixpoint interp_label l ρ :=
    match l with
    | LVar x => from_option id ⊥ (ρ !! x)
    | LLabel ℓ => ℓ
    | LJoin l l' => interp_label l ρ ⊔ interp_label l' ρ
    end.

  Notation "⌊ l ⌋ₗ" := (interp_label l) (at level 0, l at level 70).

  Lemma interp_label_flowsto l1 l2 :
    l1 ⊑ₛ l2 →
    ∀ ρ, ⌊ l1 ⌋ₗ ρ ⊑ ⌊ l2 ⌋ₗ ρ.
  Proof.
    induction 1; try done; intros ?.
    - etransitivity; eauto.
    - apply ord_bottom.
    - apply ord_top.
    - by apply join_ord.
  Qed.

  Lemma interp_label_ren1 l ℓ ρ :
    ⌊ l.[ren (+1)] ⌋ₗ (ℓ :: ρ) = ⌊ l ⌋ₗ ρ.
  Proof.
    induction l; last done.
    - by destruct x.
    - simpl. by rewrite IHl1 IHl2.
  Qed.

  Lemma interp_label_weaken l ρ1 ρ2 ξ n m :
    n = length ρ1 →
    m = length ξ →
    ⌊ l.[upn n (ren (+m))] ⌋ₗ (ρ1 ++ ξ ++ ρ2)
    = ⌊ l ⌋ₗ (ρ1 ++ ρ2).
  Proof.
    move=> -> ->. move: ρ1 ρ2 ξ. induction l; auto; simpl.
    - induction x; intros ρ1 ρ2 ξ.
      + destruct ρ1, ρ2; induction ξ; auto.
      + destruct ρ1; [induction ξ; auto|].
        asimpl. rewrite interp_label_ren1. by eapply IHx.
    - intros ?? ξ. by rewrite <- (IHl1 _ _ ξ), <- (IHl2 _ _ ξ).
  Qed.

  Lemma interp_label_subst_up l l' ρ1 ρ2 :
    ⌊ l.[upn (strings.length ρ1) (l' .: ids)] ⌋ₗ (ρ1 ++ ρ2)
    = ⌊ l ⌋ₗ (ρ1 ++ ⌊ l' ⌋ₗ ρ2 :: ρ2).
  Proof.
    move: ρ1 ρ2. induction l; auto; simpl.
    - induction x; intros ρ1 ρ2.
      + by destruct ρ1.
      + destruct ρ1; [done|].
        asimpl. rewrite interp_label_ren1 //.
    - intros. rewrite IHl1 IHl2 //.
  Qed.

  Lemma interp_label_subst1 l l' ρ :
    ⌊ l.[l'/] ⌋ₗ ρ = ⌊ l ⌋ₗ (⌊ l' ⌋ₗ ρ :: ρ).
  Proof.
    apply (interp_label_subst_up _ _ []).
  Qed.

  Lemma interp_label_join_ord_inv (ℓ1 ℓ2 ℓ3 : label_term) :
    ℓ1 ⊔ₛ ℓ2 ⊑ₛ ℓ3 →
    ∀ ρ, ⌊ ℓ1 ⌋ₗ ρ ⊑ ⌊ ℓ3 ⌋ₗ ρ ∧ ⌊ ℓ2 ⌋ₗ ρ ⊑ ⌊ ℓ3 ⌋ₗ ρ.
  Proof.
    move=> /interp_label_flowsto /= ??.
    apply join_ord_inv=> //.
  Qed.


End logrel.

Notation "⌊ l ⌋ₗ" := (interp_label l) (at level 0, l at level 70).
