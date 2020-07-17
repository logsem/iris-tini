From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.
From IC.prelude Require Import base.

Section ic_right.
  Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).

  Typeclasses Transparent ICC_state_interp ICC_modality.

  Definition icd_right : ICData Λ Σ :=
    {| ICD_state_interp := ICD_SI;
       ICD_Extra := [Prod];
       ICD_modality_index := [Prod nat];
       ICD_modality_bind_condition k k' f Ξ :=
         k' ≤ k ∧ (∀ x, f x = k - k') ∧ Ξ = λ _, id;
       ICD_modality k E n Φ := (|={E}[∅]▷=>^(n + k) |={E}=> Φ tt)%I;
    |}.

  Global Instance ICC_right : ICC icd_right.
  Proof.
    split.
    - intros k E m n P Q HPQ; simpl.
      induction n; [induction k; first by apply fupd_ne|]; simpl.
      + by rewrite IHk.
      + by rewrite IHn.
    - iIntros (k E1 E2 n P Q HE) "HPQ HP"; simpl.
      iApply step_fupdN_mask_mono; first done.
      iApply (step_fupdN_wand with "HP").
      iIntros "H"; iApply fupd_mask_mono; last iApply "HPQ"; done.
    - intros k E n P; simpl.
      induction n; simpl; first done.
      iIntros "HP". iApply step_fupd_intro; first set_solver.
      by iNext; iApply IHn.
    - intros idx idx' f g E n m P (Hidx&Hf&->); simpl in *.
      iIntros "HP".
      rewrite Hf.
      replace (n + m + idx) with (n + idx' + (m + (idx - idx'))) by lia.
      rewrite -(step_fupdN_plus (n + idx')).
      iApply (step_fupdN_wand with "HP").
      iIntros "H".
      by destruct (m + (idx - idx')); simpl; iMod "H".
  Qed.

  Global Instance IC_right_is_outer_fupd idx :
    ICMIsOuterModal icd_right idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance IC_right_is_outer_bupd idx :
    ICMIsOuterModal icd_right idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance IC_right_is_outer_except_0 idx :
    ICMIsOuterModal icd_right idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance IC_right_is_inner_fupd idx :
    ICMIsInnerModal icd_right idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">?".
  Qed.

  Global Instance IC_right_is_inner_bupd idx :
    ICMIsInnerModal icd_right idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">?".
  Qed.

  Global Instance IC_right_is_inner_except_0 idx :
    ICMIsInnerModal icd_right idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">>?".
  Qed.

  (* Global Instance IC_right_SupportsAtomicShift idx : *)
  (*   ICMSupportsAtomicShift icd_right idx. *)

  Global Program Instance IC_right_SplitForStep idx :
    ICMSplitForStep icd_right idx :=
    {|
      ICM_split_for_step_M1 E P := |={E, ∅}=> ▷ P;
      ICM_split_for_step_M2 E P := |={∅, E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (idx n E P) "HP /=".
    rewrite /ICC_modality /ICD_modality /=.
    destruct n; simpl.
    - by repeat iMod "HP".
    - by iMod "HP"; iModIntro; iNext; iMod "HP".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iMod "HP"; iModIntro; iApply "HPQ".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    iMod "HP"; iModIntro. by iApply "HPQ".
  Qed.

  Lemma ic_right_bind K `{!LanguageCtx K} E e Φ n m k :
    n = m + k →
    IC@{icd_right, m} e @ E {{ v; m,
      IC@{icd_right, k} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ IC@{icd_right, n} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros (?) "?".
    iApply (@ic_bind _ _ _ ICC_right K _ _ _ _ (λ _, id)); eauto.
    split_and!; simpl; auto with lia.
  Qed.

  Lemma ICC_right_modality_le k k' E n Φ:
    k' ≤ k →
    ICC_modality icd_right k' E n Φ ⊢ ICC_modality icd_right k E n Φ.
  Proof.
    iIntros (Hk) "H".
    rewrite /ICC_modality /=.
    replace (n + k) with (n + k' + (k - k')) by lia.
    rewrite -(step_fupdN_plus (n + k')).
    iApply step_fupdN_mono; last eauto.
    by iIntros "?"; iApply step_fupdN_intro.
  Qed.

  Lemma ic_right_intro k k' E e Φ :
    k' ≤ k →
    IC@{icd_right, k' } e @ E {{ Φ }} ⊢ IC@{icd_right, k } e @ E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    rewrite ic_eq /ic_def.
    iIntros (σ1 σ2 v n Hr) "Hi".
    iApply (ICC_right_modality_le); first done.
    iApply "H"; eauto.
  Qed.

  Lemma ic_indexed_step_fupd_index_step_fupd k k' E e Φ :
    (|={E}[∅]▷=>^k' IC@{icd_right, k } e @ E {{ Φ }})%I
    ⊢ IC@{icd_right, k' + k } e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite ic_eq /ic_def.
    iIntros (σ1 σ2 v n Hr) "Hi".
    rewrite /ICC_modality /=.
    rewrite plus_comm -plus_assoc (plus_comm _ n).
    iApply step_fupdN_plus.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iApply "H"; eauto.
  Qed.

End ic_right.

Section lifting.

Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_fupd_lift_step  E Φ e1 n :
  to_val e1 = None →
    (∀ σ1, ICD_SI σ1 -∗
      |={E, ∅}=>
     ▷ ∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (ICD_SI σ2 ∗ IC@{icd_right ICD_SI, n}
                    e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (ic_lift_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_pure_step  E Φ e1 n :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_right ICD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_right_lift_atomic_step E Φ e1 n:
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (ICD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (ic_lift_atomic_step (icd_right ICD_SI) n E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_atomic_det_step E Φ e1 n :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     (▷ ∃ v2 σ2,
           ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> ICD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_atomic_det_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_pure_det_step  E Φ e1 e2 k :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_right ICD_SI, k} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_right ICD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_det_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_right_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ k :
  PureExec φ n e1 e2 →
  φ →
  ▷^n IC@{icd_right ICD_SI, k} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ IC@{icd_right ICD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (ic_pure_step (icd_right ICD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply step_fupd_intro; first set_solver.
  iNext.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section ic_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_right_lift_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_right ICD_SI, n}
                     e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (ic_lift_head_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma ic_right_lift_pure_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_right ICD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_head_step (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_right_lift_atomic_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     ▷ ∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (ICD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
     ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (ic_lift_atomic_head_step
              (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_pure_det_head_step  E Φ e1 e2 n :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_right ICD_SI, n} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_det_head_step
            (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

End ic_ectx_lifting.

Section ic_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_right_lift_head_step' E Φ e1 n :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_right ICD_SI, n}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_head_step' (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_pure_head_step'  E Φ e1 n :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   ▷ (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       IC@{icd_right ICD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_head_step'
            (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_right_lift_atomic_head_step'  E Φ e1 n:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
      ▷ (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
          ={∅, E}=∗ (ICD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1)))
    ⊢ IC@{icd_right ICD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (ic_lift_atomic_head_step'
               (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_right_lift_pure_det_head_step'  E Φ e1 e2 k:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  IC@{icd_right ICD_SI, k} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_right ICD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_det_head_step'
            (icd_right ICD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

End ic_ectxi_lifting.

Section basic_soundness.
Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Lemma ic_right_adequacy_basic  E e σ Φ k :
  ICD_SI σ ∗ IC@{icd_right ICD_SI, k} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ),
      |={E}[∅]▷=>^(nstps rd + k)
        |={E}=> ICD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (ic_adequacy_basic (icd_right ICD_SI) k E e σ (λ v n _, Φ v n)).
Qed.

End basic_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ} {SI_data : Type} (ICD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Program Instance right_Initialization SSI `{!InitData SSI} k :
  Initialization
    unit
    (λ x : invG_pack Σ SI_data, icd_right (ICD_SI (PIG_cnt x)))
    (λ x, @ICC_right Λ Σ _ (ICD_SI (PIG_cnt x)))
    (λ _, k) :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x);
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_ICCM_soundness_arg := unit;
  initialization_ICCM_soundness_laters n _ := S (S n + k);
  initialization_modality_initializer _ _ := True;
  initialization_ICCM_soundness_fun _ := tt;
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  intros; simpl.
  iApply (init_data (λ x, _ ∗ SSI (PIG_cnt x)))%I.
Qed.
Next Obligation.
Proof.
  iIntros (?? _ P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (?? k Hi P E n _) "[[Hs HE] [_ HP]]".
  iNext.
  rewrite /ICC_modality /ICD_modality /=.
  rewrite uPred_fupd_eq /uPred_fupd_def /=.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  iInduction n as [] "IH".
  { simpl.
    iInduction k as [] "IH".
    {
      iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
        by iMod "HP". }
    simpl.
    iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    iMod "HP"; iMod "Hs"; iMod "HE".
    iNext.
    iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    iMod "HP"; iMod "Hs"; iMod "HE".
    iApply ("IH" with "Hs HP HE").
  }
  simpl.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iNext.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iApply ("IH" with "Hs HP HE").
Qed.

Lemma ic_right_adequacy SSI `{!InitData SSI} (k : nat) E e σ (Ψ : val Λ → nat → Prop):
  (∀ (x : invG_pack Σ SI_data),
     SSI (PIG_cnt x) ⊢ |={⊤}=> ICD_SI (PIG_cnt x) σ ∗
                              IC@{icd_right (ICD_SI (PIG_cnt x)), k}
                              e @ E {{ v ; n,  ⌜Ψ v n⌝ }})
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (ic_adequacy _ _ _ _ (right_Initialization SSI k) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "? /="; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
