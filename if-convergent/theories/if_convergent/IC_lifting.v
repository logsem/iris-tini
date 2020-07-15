From iris.program_logic Require Import ectxi_language ectx_language lifting.
From IC.prelude Require Export reduction.
From IC.if_convergent Require Export IC.
From iris.proofmode Require Import tactics.

Section lifting.
Context `(icd : ICData Λ Σ) `{!ICC icd} idx `{!ICMSplitForStep icd idx}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → ICC_Extra → iProp Σ.

Lemma ic_lift_step E Φ e1 :
  to_val e1 = None →
   (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
      (∀ e2 σ2,
          ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
           ICM_split_for_step_M2 E
           (ICC_state_interp icd σ2 ∗
            IC@{icd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }})))
    ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv) "H". rewrite ic_eq /ic_def.
  iIntros (σ1 σ2 v n) "Hr Ho"; iDestruct "Hr" as %Hr.
  iDestruct ("H" $! σ1 with "Ho") as "H".
  inversion Hr as [|k Hs2 [e' σ'] Hs4 Hs5 Hs6]; subst; simpl in *.
  { by rewrite to_of_val in Hnv. }
  iApply ICM_split_for_step_split.
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "Hcont".
  iDestruct ("Hcont" $! e' σ' with "[]") as "Hrest"; first done.
  iApply ICM_split_for_step_M2_mono; iFrame.
  iIntros "[Ho Hrest]".
  by iApply "Hrest".
Qed.

(** Derived lifting lemmas. *)

Lemma ic_lift_pure_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E
     (∀ σ1 e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
        IC@{icd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv Hpr) "H".
  iApply ic_lift_step; auto.
  iIntros (σ1) "Hsi".
  iApply (ICM_split_for_step_M1_mono with "[Hsi] H"); iFrame.
  iIntros "H".
  iIntros (e2 σ2 Hpstp).
  iApply (ICM_split_for_step_M2_mono with "[Hsi] H"); iFrame.
  iIntros "H".
  iSpecialize ("H" with "[]"); eauto.
  iFrame.
  by rewrite (Hpr _ _ _ Hpstp).
Qed.

Lemma ic_lift_atomic_step E Φ e1 :
  Atomic StronglyAtomic e1 →
  to_val e1 = None →
  (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ ICM_split_for_step_M2 E
             (ICC_state_interp icd σ2 ∗ ICC_modality icd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hatomic Hnv) "H".
  iApply ic_lift_step; auto.
  iIntros (σ1) "Hsi".
  iSpecialize ("H" with "Hsi").
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2 Hpstp).
  destruct (Hatomic _ _ _ _ _ Hpstp) as [v2 ?%of_to_val]; simplify_eq.
  iSpecialize ("H" with "[]"); eauto.
  iApply ICM_split_for_step_M2_mono; iFrame.
  iIntros "[$ H]".
  by iApply ic_value.
Qed.

Lemma ic_lift_atomic_det_step E Φ e1 :
  Atomic StronglyAtomic e1 →
  to_val e1 = None →
  (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
        (∃ v2 σ2,
            ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                        σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                        ICM_split_for_step_M2 E
                              (ICC_state_interp icd σ2 ∗
                               ICC_modality icd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hatomic Hnv) "H". iApply (ic_lift_atomic_step); first done.
  iIntros (σ1) "Ho"; iSpecialize ("H" $! _ with "Ho").
  iApply ICM_split_for_step_M1_mono; iFrame.
  iDestruct 1 as (v2 σ2 Hdet) "H".
  iIntros (v3 σ3 Hrd).
  iApply ICM_split_for_step_M2_mono; iFrame.
  iIntros "H".
  destruct (Hdet _ _ Hrd) as [? ?%of_to_val]; simplify_eq.
  iFrame.
Qed.

Lemma ic_lift_pure_det_step E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E (IC@{icd, idx}
                               e2 @ E {{ v; n | [x], Φ v (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "?". iApply (ic_lift_pure_step); eauto.
  - by intros; eapply Hpuredet.
  - iApply ICM_split_for_step_M1_mono; iFrame. iIntros "?".
    iApply ICM_split_for_step_M2_mono; iFrame. iIntros "?".
      by iIntros (e' σ σ' (->&->)%Hpuredet).
Qed.

Lemma ic_pure_step `{!Inhabited (state Λ)} E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  Nat.iter n (λ P, ICM_split_for_step_M1 E
     (ICM_split_for_step_M2 E P))
           (IC@{icd, idx} e2 @ E {{ v ; m | [x], Φ v (n + m) x }})
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH" forall (Φ); simpl; first done.
  iApply (ic_lift_pure_det_step _ _ _ e2).
  - specialize (Hsafe inhabitant).
    eauto using reducible_no_obs_reducible, reducible_not_val.
  - intros ? ? ? Hpstp.
    by destruct (pure_step_det _ _ _ _ _ Hpstp) as (?&?&?&?); simplify_eq.
  - iApply ICM_split_for_step_M1_mono; iFrame. iIntros "?".
    iApply ICM_split_for_step_M2_mono; iFrame. iIntros "H".
    by iApply ("IH" with "[H]").
Qed.

Lemma ic_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ, ICC_state_interp icd σ -∗
     ICM_split_for_step_M1 E
     ⌜stuck e σ⌝)
  ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros (Hnv) "H". rewrite ic_eq /ic_def.
  iIntros (σ1 σ2 v n) "Hr Hσ1"; iDestruct "Hr" as %Hr.
  iSpecialize ("H" $! _ with "Hσ1").
  inversion Hr as [|k Hs2 [e' σ'] Hs4 Hs5 Hs6]; subst; simpl in *.
  { by rewrite to_of_val in Hnv. }
  iApply ICM_split_for_step_split.
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "[_ Hirr]"; iDestruct "Hirr" as %Hirr.
  by case: (Hirr [] e' σ' []).
Qed.

End lifting.


(** Some derived lemmas for ectx-based languages *)
Section ic_ectx_lifting.

Context {Λ : ectxLanguage}.
Context `(icd : ICData Λ Σ) `{!ICC icd} idx `{!ICMSplitForStep icd idx}.

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → ICC_Extra → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).
Hint Resolve head_prim_reducible head_reducible_prim_step
     nf_head_red_head_red nf_head_reducible_nf_reducible : core.

Lemma ic_ectx_bind K E e idx' f g Φ :
  ICC_modality_bind_condition icd idx idx' f g →
  IC@{icd, idx'} e @ E {{ v ; n | [x],
    IC@{icd, f x} fill K (of_val v) @ E {{ w; m | [y], Φ w (n + m) (g x y) }} }}
     ⊢ IC@{icd, idx} fill K e @ E {{ Φ }}.
Proof. apply: ic_bind. Qed.

Lemma not_ectx_prim_step e1 σ1 κ e2 σ2 efs :
  sub_redexes_are_values e1 →
  ectx_language.prim_step e1 σ1 κ e2 σ2 efs → head_step e1 σ1 κ e2 σ2 efs.
Proof.
  intros Hnctx Hps.
  inversion Hps. subst.
  erewrite (Hnctx K); eauto.
  - by rewrite !fill_empty.
  - by eapply val_head_stuck.
Qed.

Hint Resolve not_ectx_prim_step : core.

Lemma ic_lift_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             ICM_split_for_step_M2 E
             (ICC_state_interp icd σ2 ∗
               IC@{icd, idx} e2 @ E {{  w; n | [x], Φ w (S n) x }})))
     ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv Hnctx) "H". iApply (ic_lift_step icd); first done.
  iIntros (σ1) "Ho".
  iSpecialize ("H" with "Ho").
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2) "%".
  iSpecialize ("H" $! e2 σ2 with "[]"); eauto.
Qed.

Lemma ic_lift_pure_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E
      (∀ σ1 e2 σ2,
          ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
          IC@{icd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "H".
  iApply (ic_lift_pure_step icd); eauto.
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iApply ICM_split_for_step_M2_mono; iFrame.
  iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

Lemma ic_lift_atomic_head_step E Φ e1:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ ICM_split_for_step_M2 E
           (ICC_state_interp icd σ2 ∗
            ICC_modality icd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "H". iApply (ic_lift_atomic_step icd); first done.
  iIntros (σ1) "Ho".
  iSpecialize ("H" with "Ho").
  iApply ICM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2) "%".
  iSpecialize ("H" $! e2 σ2 with "[]"); auto.
Qed.

Lemma ic_lift_pure_det_head_step E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E
      (IC@{icd, idx} e2 @ E {{  v; n | [x], Φ v (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof. intros. apply ic_lift_pure_det_step; eauto. Qed.

Lemma head_pure_lang :
  (∀ (e1 : expr Λ) σ1 σ2 e2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  PureLang Λ.
Proof.
  intros Hh e1 σ1 σ2 e2 Hps; simpl in *.
  inversion Hps; simpl in *; simplify_eq.
  eapply Hh; eauto.
Qed.

End ic_ectx_lifting.

Section ic_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context `(icd : ICData Λ Σ) `{!ICC icd} idx `{!ICMSplitForStep icd idx}.

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → ICC_Extra → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).
Hint Resolve head_prim_reducible head_reducible_prim_step
     nf_head_red_head_red nf_head_reducible_nf_reducible : core.

Hint Resolve ectxi_language_sub_redexes_are_values : core.

Lemma ic_lift_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             ICM_split_for_step_M2 E
             (ICC_state_interp icd σ2 ∗
              IC@{icd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }})))
     ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (??); iApply ic_lift_head_step; eauto. Qed.

Lemma ic_lift_pure_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E
      (∀ σ1 e2 σ2,
          ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
          IC@{icd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply ic_lift_pure_head_step; eauto. Qed.

Lemma ic_lift_atomic_head_step' E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICC_state_interp icd σ1 -∗
      ICM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ ICM_split_for_step_M2 E
           (ICC_state_interp icd σ2 ∗ ICC_modality icd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply ic_lift_atomic_head_step; eauto. Qed.

Lemma ic_lift_pure_det_head_step' E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ICM_split_for_step_M1 E
    (ICM_split_for_step_M2 E
      (IC@{icd, idx} e2 @ E {{ v; n | [x], Φ v (S n) x }}))
  ⊢ IC@{icd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply ic_lift_pure_det_head_step; eauto. Qed.

End ic_ectxi_lifting.
