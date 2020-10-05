From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From mwp Require Export mwp mwp_triple.
From mwp.mwp_modalities Require Export mwp_step_fupd mwp_fupd.
From logrel_ifc.lambda_sec Require Export lang lattice.

Class secG_un Σ := SecG_un {
  secG_un_invG :> invG Σ;
  secG_un_gen_heapG :> gen_heapG loc val Σ;
}.

Tactic Notation "umods" := rewrite /mwpC_modality /mwpD_modality; cbn.

Ltac inv_head_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : head_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1);
           inversion H; subst; clear H
         end.

Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Resolve to_of_val : core.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  unfold IntoVal in *;
  repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
  intros ?; apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_lam e1 e2 `{!AsVal e2} :
  PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
Proof. solve_pure_exec. Qed.

Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
  PureExec True 1 (LetIn e1 e2) e2.[e1 /].
Proof. solve_pure_exec. Qed.

Global Instance pure_seq e1 e2 `{!AsVal e1} :
  PureExec True 1 (Seq e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op a b :
  PureExec True 1 (BinOp op (Nat a) (Nat b)) (# (binop_eval op a b)).
Proof. solve_pure_exec. Qed.

Global Instance pure_if_true e1 e2 :
  PureExec True 1 (If (Bool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 :
  PureExec True 1 (If (Bool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
  PureExec True 1 (Proj1 (Pair e1 e2)) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
  PureExec True 1 (Proj2 (Pair e1 e2)) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
  PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
  PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
Proof. solve_pure_exec. Qed.

Global Instance pure_case_tapp e :
  PureExec True 1 (TApp (TLam e)) e.
Proof. solve_pure_exec. Qed.

Global Instance pure_case_tlapp e :
  PureExec True 1 (TLApp (TLLam e)) e.
Proof. solve_pure_exec. Qed.

Global Instance pure_unpackpack e1 e2 `{!AsVal e1}:
  PureExec True 1 (Unpack (Pack e1) e2) (e2.[e1/]).
Proof. solve_pure_exec. Qed.

Global Instance pure_fold e `{!AsVal e}:
  PureExec True 1 (Unfold (Fold e)) e.
Proof. solve_pure_exec. Qed.

Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section mwp_lang_lemmas.
  Context `{secG_un Σ}.

  Definition SI (σ : state) : iProp Σ := (gen_heap_ctx σ)%I.

  Lemma mwp_fupd_alloc E v Φ :
    {{| ∀ l, l ↦ v -∗ Φ (LocV l) 1 |}}@{mwpd_fupd SI}
      Alloc (# v) @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> HΦ".
    iApply mwp_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro. iIntros (v' σ2 Hstep); inv_head_step.
    assert (# v' = # (LocV l)) by auto; simplify_eq.
    iMod (@gen_heap_alloc with "Hσ1") as "(Hσ & Hl & _)"; first done.
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma mwp_fupd_load E l q v Φ :
    {{| l ↦{q} v ∗ (l ↦{q} v -∗ Φ v 1) |}}@{mwpd_fupd SI}
      Load (Loc l) @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> [Hl HΦ]".
    iApply mwp_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iDestruct (@gen_heap_valid with "Hσ1 Hl") as %?.
    iModIntro. iIntros (v' σ2 Hstep); inv_head_step.
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma mwp_fupd_store E l v v' Φ :
    {{| l ↦ v ∗ (l ↦ v' -∗ Φ UnitV 1) |}}@{mwpd_fupd SI}
      Store (Loc l) (# v') @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> [Hl HΦ]".
    iApply mwp_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro. iIntros (w σ2 Hstep); inv_head_step.
    assert (# w = # UnitV) by auto; simplify_eq.
    iMod (@gen_heap_update with "Hσ1 Hl") as "[$ Hl]".
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma mwp_step_fupd_alloc E v Φ :
    {{| ▷ ∀ l, l ↦ v -∗ Φ (LocV l) 1 |}}@{mwpd_step_fupd SI}
      Alloc (# v) @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> HΦ".
    iApply mwp_step_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    do 2 iModIntro. iIntros (v' σ2 Hstep); inv_head_step.
    assert (# v' = # (LocV l)) by auto; simplify_eq.
    iMod (@gen_heap_alloc with "Hσ1") as "(Hσ & Hl & _)"; first done.
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma mwp_step_fupd_load E l q v Φ :
    {{| ▷ l ↦{q} v ∗ ▷ (l ↦{q} v -∗ Φ v 1) |}}@{mwpd_step_fupd SI}
      Load (Loc l) @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> [Hl HΦ]".
    iApply mwp_step_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    do 2 iModIntro.
    iDestruct (@gen_heap_valid with "Hσ1 Hl") as %?.
    iIntros (v' σ2 Hstep); inv_head_step.
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma mwp_step_fupd_store E l v v' Φ :
    {{| ▷ l ↦ v ∗ ▷ (l ↦ v' -∗ Φ UnitV 1) |}}@{mwpd_step_fupd SI}
      Store (Loc l) (# v') @ E
    {{| w ; n, Φ w n |}}.
  Proof.
    iIntros "_ !> [Hl HΦ]".
    iApply mwp_step_fupd_lift_atomic_head_step'; auto.
    { intros []; inversion 1; eauto. }
    iIntros (σ1) "Hσ1".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    do 2 iModIntro. iIntros (w σ2 Hstep); inv_head_step.
    assert (# w = # UnitV) by auto; simplify_eq.
    iMod (@gen_heap_update with "Hσ1 Hl") as "[$ Hl]".
    iMod "Hclose"; iModIntro; iFrame; iModIntro.
    by iApply "HΦ".
  Qed.

End mwp_lang_lemmas.
