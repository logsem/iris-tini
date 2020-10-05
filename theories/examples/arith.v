From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas
     mwp_logrel_fupd ni_logrel_fupd_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This example is not syntactically well-typed as it relies on arithmetic
   facts for soundness. *)

(* λ x, x * 0 *)
Definition multZ : expr := (λ: $0 * #0)%E.
(* ... and type Nat @ H -L-> Nat @ L *)

Section related.
  Context `{!secG Σ}.

  Lemma multZ_related :
    [] ⊨ multZ ≤ₗ multZ : (TArrow L (TNat @ H) (TNat @ L)) @ L.
  Proof.
    iIntros (????) "_" . rewrite /interp_expr.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwp_right)); umods.
    uarrows.
    rewrite bool_decide_eq_true_2 //.
    iModIntro. repeat iSplit; iModIntro.
    - iIntros (?). unats.
      rewrite bool_decide_eq_false_2 //.
      iIntros "[Hw1 Hw2]". rewrite /interp_expr /=.
      iDestruct "Hw1" as (n1) "->".
      iDestruct "Hw2" as (n2) "->".
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      asimpl. iModIntro.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      rewrite /= !Nat.mul_0_r. iNext.
      iApply (mwp_value mwp_binary); umods.
      iApply (mwp_value mwp_right); umods.
      iModIntro. unats.
      rewrite bool_decide_eq_true_2 //; auto.
    - iIntros (?) "Hw1". unats.
      iDestruct "Hw1" as (n1) "->".
      by iIntros "%".
    - iIntros (?) "Hw1". unats.
      iDestruct "Hw1" as (n1) "->".
      by iIntros "%".
  Qed.

End related.
