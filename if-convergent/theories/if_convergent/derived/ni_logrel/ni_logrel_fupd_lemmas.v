From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From IC.prelude Require Import base.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From IC.if_convergent.derived Require Import IC_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_logrel_fupd.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ni_logrel_fupd_lemmas.
  Context {Λ Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).

  Implicit Types e : expr Λ.

  Lemma ic_un_bi_fupd_lr e e' Φ E :
    IC@{icd_fupd ICD_SI} e @ E
      {{ v; m, IC@{icd_fupd ICD_SI'} e' @ E {{ w ; k, Φ v m (w, k)}} }} -∗
      IC@{icd_logrel_fupd ICD_SI ICD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite ic_eq /ic_def /ICC_modality /= /ICC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "[Hics HSI]".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "[Hics HSI']".
    iModIntro; iFrame.
  Qed.

  Lemma ic_un_bi_fupd_rl e e' Φ E :
    IC@{icd_fupd ICD_SI'} e' @ E
      {{ v; m, IC@{icd_fupd ICD_SI} e @ E {{ w ; k, Φ w k (v, m)}} }} -∗
      IC@{icd_logrel_fupd ICD_SI ICD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite ic_eq /ic_def /ICC_modality /= /ICC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "[Hics HSI']".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "[Hics HSI]".
    iModIntro; iFrame.
  Qed.

  Lemma ic_ni_logrel_fupd_lr E1 E2 e e' Φ  :
    (|={E1,E2}=>
      IC@{icd_logrel_fupd ICD_SI ICD_SI', e'} e @ E2 {{ v; m | [x], |={E2,E1}=> Φ v m x}})
      -∗ IC@{icd_logrel_fupd ICD_SI ICD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    iMod "H".
    iSpecialize ("H" with "[] Ho"); first done.
    iSpecialize ("H" with "[] Ho'"); first done.
    by iMod "H" as "[[H $] $]".
  Qed.

End ni_logrel_fupd_lemmas.
