From Coq.ssr Require Import ssreflect.
From stdpp Require Import base prelude list gmap.

Class Lattice (A : Type) := {
    lat_equiv :> Equiv A;
    lat_equiv_equiv :> Equivalence lat_equiv;
    lat_equiv_dec :> RelDecision lat_equiv;
    join : A → A → A;
    join_proper :> Proper ((≡) ==> (≡) ==> (≡)) join;
    join_commutative :> Comm (≡) join;
    join_associative :> Assoc (≡) join;
    join_idempotent  :> IdemP (≡) join;

    bot : A;
    bot_left_id  :> LeftId (≡) bot join;
    bot_right_id :> RightId (≡) bot join;

    top : A;
    top_left_absorb :> LeftAbsorb (≡) top join;
    top_right_absorb :> RightAbsorb (≡) top join;
}.

Class SecurityLattice (label : Type) := {
   lattice :> Lattice label;
   ζ : label; (* attacker/observer *)
}.

Infix "⊔" := join (at level 50) : stdpp_scope.
Notation "⊥" := bot : stdpp_scope.
Notation "⊤" := top : stdpp_scope.

Section Order.
  Context `{lattice : Lattice label}.

  Implicit Types a b : label.

  Definition order a b := a ⊔ b ≡ b.

  Global Instance ord_reflexive : Reflexive order.
  Proof. by move=> ?; rewrite /order idemp. Qed.

  Global Instance ord_antisymmetric : Antisymmetric label (≡) order.
  Proof. by rewrite /order => x y Ho1 Ho2; rewrite -Ho1 -{1}Ho2 (comm _ x). Qed.

  Global Instance ord_transitive : Transitive order.
  Proof. by rewrite /order => ??? Ho1 Ho2; rewrite -Ho2 assoc Ho1. Qed.

  Lemma ord_bottom x : order ⊥ x.
  Proof. by rewrite /order left_id. Qed.

  Lemma ord_top x : order x ⊤.
  Proof. by rewrite /order right_absorb. Qed.

  Global Instance order_proper : Proper ((≡) ==> (≡) ==> iff) order.
  Proof. by intros x y Hxy u v Huv; rewrite /order Hxy Huv. Qed.

  Global Instance order_dec : RelDecision order.
  Proof. intros x y. by destruct (decide (x ⊔ y ≡ y)); [left|right]. Qed.

End Order.

Notation "a ⊑ b" := (order a b) (at level 70) : stdpp_scope.
Notation "a ⋢ b" := (¬ (order a b)) (at level 70) : stdpp_scope.

Hint Extern 3 => apply ord_bottom : core.
Hint Extern 6 => rewrite bot_left_id : core.
Hint Extern 6 => rewrite bot_right_id : core.

Section Lemmas.
  Context `{lattice : Lattice label}.

  Implicit Types ℓ : label.

  Lemma ord_join_left ℓ1 ℓ2: ℓ1 ⊑ ℓ1 ⊔ ℓ2.
  Proof. by rewrite /order assoc idemp. Qed.

  Lemma ord_join_right ℓ1 ℓ2: ℓ1 ⊑ ℓ2 ⊔ ℓ1.
  Proof. rewrite comm; apply ord_join_left. Qed.

  Lemma ord_join_left' ℓ1 ℓ2 ℓ3 : ℓ1 ⊑ ℓ2 → ℓ1 ⊑ ℓ2 ⊔ ℓ3.
  Proof. by rewrite /order assoc => ->. Qed.

  Lemma ord_join_right' ℓ1 ℓ2 ℓ3 : ℓ1 ⊑ ℓ3 → ℓ1 ⊑ ℓ2 ⊔ ℓ3.
  Proof. rewrite comm; apply ord_join_left'. Qed.

  Lemma join_ord_inv ℓ1 ℓ2 ℓ3 : ℓ1 ⊔ ℓ2 ⊑ ℓ3 → ℓ1 ⊑ ℓ3 ∧ ℓ2 ⊑ ℓ3.
  Proof.
    intros.
    assert (ℓ1 ⊑ ℓ1 ⊔ ℓ2) by apply ord_join_left.
    assert (ℓ2 ⊑ ℓ1 ⊔ ℓ2) by apply ord_join_right.
    split; eapply ord_transitive; eauto.
  Qed.

  Lemma join_ord ℓ1 ℓ2 ℓ3 : ℓ1 ⊑ ℓ3 → ℓ2 ⊑ ℓ3 → ℓ1 ⊔ ℓ2 ⊑ ℓ3.
  Proof. rewrite /order -join_associative => + -> //. Qed.

  Lemma ord_join_neg_left ℓ1 ℓ2 ℓ3 : ℓ1 ⋢ ℓ3 → ℓ1 ⊔ ℓ2 ⋢ ℓ3.
  Proof. move=> ? /join_ord_inv [? ?] //. Qed.

  Lemma ord_join_neg_right ℓ1 ℓ2 ℓ3 : ℓ1 ⋢ ℓ3 → ℓ2 ⊔ ℓ1 ⋢ ℓ3.
  Proof. rewrite join_commutative. apply ord_join_neg_left. Qed.

  Lemma ord_neg_left ℓ1 ℓ2 ℓ3 : ℓ1 ⊑ ℓ2 → ℓ1 ⋢ ℓ3 → ℓ2 ⋢ ℓ3.
  Proof.
    intros H1 H2. case (bool_decide (ℓ2 ⊑ ℓ3)) eqn:Heq.
    - apply bool_decide_eq_true in Heq.
      assert (ℓ1 ⊑ ℓ3); first by etransitivity.
      contradiction.
    - by apply bool_decide_eq_false in Heq.
  Qed.

End Lemmas.

(** Example lattices *)
Section TwoPoint.
  Inductive tplabel := L | H.

  Global Instance tplabel_eq_dec : EqDecision tplabel.
  Proof. intros ??; rewrite /Decision; decide equality. Qed.

  Implicit Types ℓ : tplabel.

  Definition join_tplabel ℓ ℓ' :=
    match ℓ with
    | L => ℓ'
    | H => H
    end.

  Instance tp_commutative : Comm (=) join_tplabel.
  Proof. by do 2 case.  Qed.

  Instance tp_associative : Assoc (=) join_tplabel.
  Proof. by do 3 case.  Qed.

  Instance tp_idempotent : IdemP (=) join_tplabel.
  Proof. by case. Qed.

  Instance L_left_id : LeftId (=) L join_tplabel.
  Proof. by case. Qed.

  Instance L_right_id : RightId (=) L join_tplabel.
  Proof. by case. Qed.

  Instance H_left_absorb : LeftAbsorb (=) H join_tplabel.
  Proof. by case. Qed.

  Instance H_right_absorb : RightAbsorb (=) H join_tplabel.
  Proof. by case. Qed.

  Global Instance tpLattice : Lattice tplabel :=
    {
      join := join_tplabel;
      lat_equiv := (=);
      bot := L;
    }.

End TwoPoint.
