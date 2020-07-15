From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ic_step_fupd.
  Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).

  Typeclasses Transparent ICC_state_interp ICC_modality.

  Definition icd_step_fupd : ICData Λ Σ :=
    {| ICD_state_interp := ICD_SI;
       ICD_Extra := [Prod];
       ICD_modality_index := [Prod];
       ICD_modality_bind_condition idx idx' f Ξ := Ξ = λ _, id;
       ICD_modality idx E n Φ := (|={E, ∅}▷=>^n |={E}=> Φ tt)%I;
    |}.

  Global Instance ICC_step_fupd : ICC icd_step_fupd.
  Proof.
    split.
    - intros idx E m n P Q HPQ; simpl.
      induction n; simpl; first by apply fupd_ne.
      by rewrite IHn.
    - iIntros (idx E1 E2 n P Q HE) "HPQ HP"; simpl.
      iSpecialize ("HPQ" $! tt).
      iInduction n as [] "IH"; simpl.
      + iApply fupd_wand_l; iFrame. by iApply fupd_mask_mono.
      + iApply step_fupd_mask_mono; last (iMod "HP"; iModIntro); try set_solver.
        iNext. iMod "HP"; iModIntro.
        iApply ("IH" with "HPQ HP").
    - intros idx E n P; simpl.
      induction n; simpl; first done.
      iIntros "HP". iApply step_fupd_intro; first set_solver.
      by iNext; iApply IHn.
    - intros idx idx' f g E n m P ->; simpl.
      iIntros "HP".
      iInduction n as [] "IH"; simpl; first by destruct m; iMod "HP".
      iMod "HP"; iModIntro; iNext; iMod "HP"; iModIntro.
        by iApply "IH".
  Qed.

  Global Instance IC_step_fupd_is_outer_fupd idx :
    ICMIsOuterModal icd_step_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; simpl; by iMod "H".
  Qed.

  Global Instance IC_step_fupd_is_outer_bupd idx :
    ICMIsOuterModal icd_step_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; simpl; by iMod "H".
  Qed.

  Global Instance IC_step_fupd_is_outer_except_0 idx :
    ICMIsOuterModal icd_step_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    destruct n; simpl; by iMod "H".
  Qed.

  Global Instance IC_step_fupd_is_inner_fupd idx :
    ICMIsInnerModal icd_step_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iInduction n as [] "IH"; simpl; first by iMod "H".
    iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
    by iApply "IH".
  Qed.

  Global Instance IC_step_fupd_is_inner_bupd idx :
    ICMIsInnerModal icd_step_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iInduction n as [] "IH"; simpl; first by iMod "H".
    iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
    by iApply "IH".
  Qed.

  Global Instance IC_step_fupd_is_inner_except_0 idx :
    ICMIsInnerModal icd_step_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    iInduction n as [] "IH"; simpl; first by repeat iMod "H".
    iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
    by iApply "IH".
  Qed.

  Global Instance IC_step_fupd_SupportsAtomicShift idx :
    ICMSupportsAtomicShift icd_step_fupd idx.
  Proof.
    rewrite /ICMSupportsAtomicShift /ICC_modality /ICD_modality /=.
    iIntros (n E1 E2 P Hn) "H".
    destruct n as [|[]]; simpl; last lia.
    - by repeat iMod "H".
    - repeat iMod "H". iModIntro. iNext.
      by repeat iMod "H".
  Qed.

  Global Program Instance IC_step_fupd_SplitForStep idx :
    ICMSplitForStep icd_step_fupd idx :=
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

  Lemma ic_step_fupd_bind K `{!LanguageCtx K}  E e Φ :
    IC@{icd_step_fupd} e @ E {{ v; m,
      IC@{icd_step_fupd} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ IC@{icd_step_fupd} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros "?".
    by iApply (@ic_bind _ _ _ ICC_step_fupd K _ _ _ _ (λ _, id)); eauto.
  Qed.

End ic_step_fupd.

Section lifting.

Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_step_fupd_lift_step  E Φ e1 :
  to_val e1 = None →
    (∀ σ1, ICD_SI σ1 -∗
      |={E, ∅}=>
     ▷ ∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (ICD_SI σ2 ∗ IC@{icd_step_fupd ICD_SI}
                    e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (ic_lift_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_step_fupd_lift_pure_step  E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_step_fupd ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_step_fupd_lift_atomic_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (ICD_SI σ2 ∗ |={E}=> Φ v2 1))
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (ic_lift_atomic_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl.
Qed.

Lemma ic_step_fupd_lift_atomic_det_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     (▷ ∃ v2 σ2,
           ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> ICD_SI σ2 ∗ |={E}=> Φ v2 1))
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_atomic_det_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_step_fupd_lift_pure_det_step  E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_step_fupd ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_det_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_step_fupd_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n IC@{icd_step_fupd ICD_SI} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (ic_pure_step (icd_step_fupd ICD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply step_fupd_intro; first set_solver.
  iNext.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

Lemma ic_step_fupd_stuck E Φ e :
  to_val e = None →
  (∀ σ, ICD_SI σ ={E, ∅}=∗ ▷ ⌜stuck e σ⌝)
  ⊢ IC@{icd_step_fupd ICD_SI} e @ E {{ (λ v n _, Φ v n) }}.
Proof.
  iIntros (?) "H".
  iApply (@ic_lift_stuck _ _ _ _ _ _); first done.
  iExact "H".
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

Lemma ic_step_fupd_lift_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_step_fupd ICD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (ic_lift_head_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma ic_step_fupd_lift_pure_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_step_fupd ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_head_step (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_step_fupd_lift_atomic_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     ▷ ∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (ICD_SI σ2 ∗ |={E}=> Φ v2 1))
     ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (ic_lift_atomic_head_step
              (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_step_fupd_lift_pure_det_head_step  E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_step_fupd ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_det_head_step
            (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
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

Lemma ic_step_fupd_lift_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_step_fupd ICD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_head_step' (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_step_fupd_lift_pure_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   ▷ (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       IC@{icd_step_fupd ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_head_step'
            (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_step_fupd_lift_atomic_head_step'  E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
      ▷ (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
          ={∅, E}=∗ (ICD_SI σ2 ∗ |={E}=> Φ v2 1)))
    ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (ic_lift_atomic_head_step'
               (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_step_fupd_lift_pure_det_head_step'  E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  IC@{icd_step_fupd ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_step_fupd ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_det_head_step'
            (icd_step_fupd ICD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

End ic_ectxi_lifting.

Section basic_soundness.
Context {Λ Σ} `{!invG Σ} (ICD_SI : state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Lemma ic_step_fupd_adequacy_basic  E e σ Φ :
  ICD_SI σ ∗ IC@{icd_step_fupd ICD_SI} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ),
      |={E, ∅}▷=>^(nstps rd)
        |={E}=> ICD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (ic_adequacy_basic (icd_step_fupd ICD_SI) _ E e σ (λ v n _, Φ v n)).
Qed.

End basic_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ} {SI_data : Type} (ICD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

 Program Instance step_fupd_Initialization SSI `{!InitData SSI}:
  Initialization
    unit
    (λ H : invG_pack Σ SI_data, icd_step_fupd (ICD_SI (PIG_cnt H)))
    (λ H, @ICC_step_fupd Λ Σ _ (ICD_SI (PIG_cnt H)))
    (λ _, tt) :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x);
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_ICCM_soundness_arg := unit;
  initialization_ICCM_soundness_laters n _ := S (S n);
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
  iIntros (?? P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (? ? Hi P E n _) "[[Hs HE] [_ HP]]".
  iNext.
  rewrite /ICC_modality /ICD_modality /=.
  rewrite uPred_fupd_eq /uPred_fupd_def /=.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  iInduction n as [] "IH".
  { iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    by iMod "HP". }
  simpl.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iNext.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iApply ("IH" with "Hs HP HE").
Qed.

Lemma ic_step_fupd_adequacy SSI `{!InitData SSI} E e σ (Ψ : val Λ → nat → Prop):
  (∀ (Hcnd : invG_pack Σ SI_data),
      SSI (PIG_cnt Hcnd) ⊢
        |={⊤}=> (ICD_SI (PIG_cnt Hcnd) σ ∗
                       IC@{icd_step_fupd (ICD_SI (PIG_cnt Hcnd))}
                       e @ E {{ v ; n,  ⌜Ψ v n⌝ }}))
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (ic_adequacy _ _ _ _ (step_fupd_Initialization SSI) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "? /="; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
