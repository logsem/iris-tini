From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From IC.prelude Require Import base.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From IC.if_convergent.derived Require Import IC_step_fupd IC_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right
     IC_logrel_fupd.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ni_logrel_lemmas.
  Context {Λ Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).

  Implicit Types e : expr Λ.

  Lemma ic_un_bi_lr e e' Φ E :
    IC@{icd_step_fupd ICD_SI} e @ E
      {{ v; m, IC@{icd_step_fupd ICD_SI'} e' @ E {{ w ; k, Φ v m (w, k)}} }} -∗
      IC@{icd_left ICD_SI ICD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite ic_eq /ic_def /ICC_modality /= /ICC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI]".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI']".
    rewrite -Nat.add_sub_assoc // Nat.sub_diag Nat.add_0_r Nat.sub_diag /=.
    iModIntro; iFrame.
  Qed.

  Lemma ic_un_bi_rl e e' Φ E :
    IC@{icd_step_fupd ICD_SI'} e' @ E
      {{ v; m, IC@{icd_step_fupd ICD_SI} e @ E {{ w ; k, Φ w k (v, m)}} }} -∗
      IC@{icd_left ICD_SI ICD_SI', e'} e @ E {{ Φ}}.
  Proof.
    do 2 rewrite ic_eq /ic_def /ICC_modality /= /ICC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI']".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI]".
    rewrite minus_plus Nat.sub_diag /=.
    iModIntro; iFrame.
  Qed.

  Lemma ic_double_atomic_lr a E1 E2 e e' Φ `{!Atomic a e, !Atomic a e'} :
    (|={E1,E2}=>
     IC@{icd_step_fupd ICD_SI} e @ E2
       {{ v; m,
             IC@{icd_fupd ICD_SI'}
               e' @ E2 {{ w ; k, |={E2,E1}=> Φ v m (w, k)}} }})
      -∗ IC@{icd_left ICD_SI ICD_SI', e'} e @ E1 {{ Φ}}.
  Proof.
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd').
    destruct (n' + n) as [|m] eqn:Hnn; simpl in *.
    - assert (n = 0) as -> by lia.
      assert (n' = 0) as -> by lia.
      iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      iMod "H" as "[H Ho]".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      iMod "H" as "[H Ho']".
      iMod "H".
      iModIntro.
      rewrite /ICC_state_interp /=.
      iFrame.
    - iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      destruct n as [|[]]; last lia; simpl in *.
      + iMod "H" as "[H Ho]".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho'").
        iMod "H" as "[H Ho']".
        iMod "H".
        iApply step_fupd_intro; first set_solver.
        iNext.
        iApply step_fupdN_intro. iModIntro.
        rewrite /ICC_state_interp /=.
        iFrame.
      + iMod "H".
        iModIntro.
        iNext.
        iMod "H".
        iMod "H" as "[H Ho]".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho'").
        iMod "H" as "[H Ho']".
        iMod "H".
        iModIntro.
        iApply step_fupdN_intro. iModIntro.
        rewrite /ICC_state_interp /=.
        iFrame.
  Qed.

  Lemma ic_double_atomic_rl a E1 E2 e e' Φ `{!Atomic a e, !Atomic a e'} :
    (|={E1,E2}=>
     IC@{icd_step_fupd ICD_SI'} e' @ E2
       {{ v; m,
             IC@{icd_fupd ICD_SI}
               e @ E2 {{ w ; k, |={E2,E1}=> Φ w k (v, m)}} }})
      -∗ IC@{icd_left ICD_SI ICD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd').
    destruct (n' + n) as [|m] eqn:Hnn; simpl in *.
    - assert (n = 0) as -> by lia.
      assert (n' = 0) as -> by lia.
      iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      iMod "H" as "[H Ho']".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      iMod "H" as "[H Ho]".
      iMod "H".
      iModIntro.
      rewrite /ICC_state_interp /=.
      iFrame.
    - iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      destruct n' as [|[]]; last lia; simpl in *.
      + iMod "H" as "[H Ho']".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho").
        iMod "H" as "[H Ho]".
        iMod "H".
        iApply step_fupd_intro; first set_solver.
        iNext.
        iApply step_fupdN_intro. iModIntro.
        rewrite /ICC_state_interp /=.
        iFrame.
      + iMod "H".
        iModIntro.
        iNext.
        iMod "H".
        iMod "H" as "[H Ho']".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho").
        iMod "H" as "[H Ho]".
        iMod "H".
        iModIntro.
        iApply step_fupdN_intro. iModIntro.
        rewrite /ICC_state_interp /=.
        iFrame.
  Qed.

  Lemma ni_logrel_fupd_ni_logrel E1 E2 e e' Φ  :
    ((∀ σ, ICD_SI σ ={E1, ∅}=∗ ⌜reducible e σ⌝) ∨
     (∀ σ, ICD_SI' σ ={E1, ∅}=∗ ⌜reducible e' σ⌝))
    ∧
    (|={E1,E2}=>
      ▷ IC@{icd_logrel_fupd ICD_SI ICD_SI', e'} e @ E2 {{ v; m | [x], |={E2,E1}=> Φ v m x}})
      -∗ IC@{icd_left ICD_SI ICD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite ic_eq /ic_def /ICC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    destruct (n' + n) eqn:Hnn'; simpl in *.
    { apply Nat.eq_add_0 in Hnn' as [-> ->]; simpl in *.
      iDestruct "H" as "[[H|H] _]".
      - inversion Hrd; simplify_eq.
        iMod ("H" with "Ho") as %Hred%reducible_not_val.
        by rewrite to_of_val in Hred.
      - inversion Hrd'; simplify_eq.
        iMod ("H" with "Ho'") as %Hred'%reducible_not_val.
        by rewrite to_of_val in Hred'. }
    iDestruct "H" as "[_ H]".
    iMod "H".
    iMod (fupd_intro_mask' _ ∅) as "Hcl"; first set_solver.
    iModIntro.
    iNext.
    iSpecialize ("H" with "[] Ho"); first done.
    iSpecialize ("H" with "[] Ho'"); first done.
    iMod "Hcl" as "_".
    iMod "H" as "[[H Ho] Ho']".
    iMod "H".
    iModIntro.
    iApply step_fupdN_intro.
    rewrite /ICC_state_interp /ICD_state_interp /=.
    by iModIntro; iFrame.
  Qed.

End ni_logrel_lemmas.
