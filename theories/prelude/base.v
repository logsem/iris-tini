From iris.algebra Require Export base.
From iris.base_logic Require Import upred.
From iris.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants.
From Autosubst Require Export Autosubst.
From mwp Require Export mwp.
Import uPred.

Canonical Structure varC := leibnizO var.

Class IdsLemmas (term : Type) {Ids_term : Ids term} := {
  ids_inj x y : ids x = ids y → x = y
}.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}
          {IdsLeamms_term : IdsLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (destruct (lt_dec _ _) || asimpl || rewrite IH); auto with lia.
  Qed.

End Autosubst_Lemmas.

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (MWP@{_} _ {{ _ }})%I ≡ (MWP@{_} _ {{ _ }})%I => apply mwp_proper=>???
  | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply intuitionistically_proper
  | |- (<pers> _)%I ≡ (<pers> _)%I => apply persistently_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  | |- (|={_,_}=> _)%I ≡ (|={_,_}=> _)%I => apply fupd_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply wand_proper
  | |- (fixpoint _)%I ≡ (fixpoint _)%I => apply fixpoint_proper=>??
  end.

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).
