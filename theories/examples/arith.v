From iris.proofmode Require Import tactics.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas
     IC_logrel_fupd ni_logrel_fupd_lemmas.
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
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (ic_right)); umods.
    uarrows.
    rewrite bool_decide_eq_true_2 //.
    iModIntro. repeat iSplit; iModIntro.
    - iIntros (?). unats.
      rewrite bool_decide_eq_false_2 //.
      iIntros "[Hw1 Hw2]". rewrite /interp_expr /=.
      iDestruct "Hw1" as (n1) "->".
      iDestruct "Hw2" as (n2) "->".
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      asimpl. iModIntro.
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      rewrite /= !Nat.mul_0_r. iNext.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value ic_right); umods.
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
