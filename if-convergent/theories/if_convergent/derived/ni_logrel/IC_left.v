From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From IC.if_convergent.derived.ni_logrel Require Import IC_right.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ic_left.
  Context {Λ Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).
  Typeclasses Transparent ICC_state_interp ICC_modality.

  Definition icd_left : ICData Λ Σ :=
    {| ICD_state_interp := ICD_SI;
       ICD_Extra := [Prod val Λ; nat];
       ICD_modality_index := [Prod expr Λ];
       ICD_modality_bind_condition e1 e2 f g :=
         ∃ K (_: LanguageCtx K),
           e1 = K e2 ∧ g = (λ x y, (y.1, x.2 + y.2)) ∧
           ∀ v k, f (v, k) = K (of_val v);
      ICD_modality idx E n Φ :=
        IC@{icd_right ICD_SI', n} idx @ E {{ w; k, Φ (w, k) }}%I;
    |}.

  Global Instance ICC_left : ICC icd_left.
  Proof.
    split.
    - intros idx E m n ? ? ?; simpl. apply ic_ne.
      intros ? ? ?; auto.
    - intros idx E1 E2 n Φ Ψ HE; simpl.
      iIntros "HP Hic".
      iApply (ic_strong_mono_wand _ _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      by iIntros (? ? ?) "?"; iApply "HP".
    - iIntros (idx E n Φ) "H";simpl.
      iApply ic_right_intro; last eauto. simpl; lia.
    - intros e e' f g E n m Φ (K & HK & He & Hg & Hf); simplify_eq.
      iIntros "H"; simpl.
      iApply (ic_right_bind _ _ _ _ _ _ n m); simpl; first done.
      iApply (ic_strong_mono_wand _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      iIntros (v l _); rewrite Hf /=.
      iIntros "H".
      iApply (ic_strong_mono_wand _ _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      by iIntros (? j _) "?".
  Qed.

  Global Instance ICC_left_is_outer_fupd idx :
    ICMIsOuterModal icd_left idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance ICC_left_is_outer_bupd idx :
    ICMIsOuterModal icd_left idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance ICC_left_is_outer_except_0 idx :
    ICMIsOuterModal icd_left idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsOuterModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance ICC_left_is_inner_fupd idx :
    ICMIsInnerModal icd_left idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    by iApply (ic_fupd _ _ _ _ (λ v m _, _)).
  Qed.

  Global Instance ICC_left_is_inner_bupd idx :
    ICMIsInnerModal icd_left idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    by iApply (ic_bupd _ _ _ _ (λ v m _, _)).
  Qed.

  Global Instance ICC_left_is_inner_except_0 idx :
    ICMIsInnerModal icd_left idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /ICMIsInnerModal /ICC_modality /ICD_modality /=.
    iIntros (E n P) "H".
    by iApply (ic_except_0 _ _ _ _ (λ v m _, _)).
  Qed.

  (* Global Instance ICC_left_SupportsAtomicShift idx : *)
  (*   ICMSupportsAtomicShift icd_left idx. *)
  (* Proof. *)
  (*   rewrite /ICMSupportsAtomicShift /ICC_modality /ICD_modality /=. *)
  (*   iIntros (n E1 E2 Φ Hn) "H". *)
  (*   iApply (ic_shift (icd_indexed_step_fupd ICD_SI')); *)
  (*     eauto using IC_indexed_step_fupd_AlwaysSupportsShift. *)
  (* Qed. *)

  Global Program Instance ICC_left_SplitForStep idx :
    ICMSplitForStep icd_left idx :=
    {|
      ICM_split_for_step_M1 E P := |={E, ∅}=> ▷ P;
      ICM_split_for_step_M2 E P := |={∅, E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (e n E P) "HP /=".
    rewrite /ICC_modality /ICD_modality /=.
    by iApply (ic_indexed_step_fupd_index_step_fupd _ _ 1).
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

  Lemma ic_left_strong_bind
        K `{!LanguageCtx K} K' `{!LanguageCtx K'} E e e' Φ :
    IC@{icd_left, e'} e @ E {{ v; m | w ; k,
      IC@{icd_left, K' (of_val w)}
        K (of_val v) @ E {{ w; n | u ; y, Φ w (m + n) (u, (k + y)) }} }}
    ⊢ IC@{icd_left, K' e'} K e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (@ic_bind _ _ _ ICC_left K _ _ e'
                     (λ '(v, k), K' (of_val v))
                     (λ x y, (y.1, x.2 + y.2))).
    { rewrite /ICC_modality_bind_condition /=; eauto. }
    iApply ic_mono; last eauto.
    intros ? ? []; auto.
  Qed.

Lemma ic_left_change_of_index e1' e2' f E e Φ :
  (∀ Ψ n,
      IC@{icd_right ICD_SI', n}
        e1' @ E {{ v; n | [_], Ψ (f (v, n)) }} -∗
        IC@{icd_right ICD_SI', n}
        e2' @ E {{ v; n | [_], Ψ (v, n) }})
  -∗ IC@{icd_left, e1'} e @ E {{ λ v n x, Φ v n (f x) }}
  -∗ IC@{icd_left, e2'} e @ E {{ Φ }}.
Proof.
  iIntros "Hm H".
  iApply (ic_change_of_index icd_left with "[Hm] H").
  iIntros (Ψ n) "H".
  by iApply "Hm".
Qed.

Lemma ic_left_pure_step_index `{!Inhabited (state Λ)}  e1' e2' E e Φ φ n :
  PureExec φ n e2' e1' →
  φ →
  IC@{icd_left, e1'} e @ E {{ v;k | w;m, Φ v k (w, n + m) }}
  ⊢ IC@{icd_left, e2'} e @ E {{ v;m | [x], Φ v m x }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (ic_left_change_of_index _ _ (λ '(v, m), (v, n + m))).
  - iIntros (??) "H".
    iApply ic_right_pure_step; first done.
    iNext. iApply "H".
  - iApply ic_wand_r; iSplitL; first iApply "Hic".
    by iIntros (??[]) "Hic".
Qed.

End ic_left.

Section lifting.

Context {Λ Σ} `{!invG Σ} (ICD_SI ICD_SI': state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → val Λ * nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_fupd_lift_step idx E Φ e1 :
  to_val e1 = None →
    (∀ σ1, ICD_SI σ1 -∗
      |={E, ∅}=>
     ▷ ∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (ICD_SI σ2 ∗ IC@{icd_left ICD_SI ICD_SI', idx}
                    e2 @ E {{ v; n| [x], Φ v (S n) x }}))
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "?".
  iApply (ic_lift_step (icd_left ICD_SI ICD_SI') idx E); simpl; auto.
Qed.

Lemma ic_left_lift_pure_step idx E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_left ICD_SI ICD_SI', idx} e2 @ E
        {{ v; n | [x], Φ v (S n) x }})
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_step
            (icd_left ICD_SI ICD_SI') idx E);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_left_lift_atomic_step idx E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (ICD_SI σ2 ∗
                        IC@{icd_right ICD_SI', 0}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (??).
  by iApply (ic_lift_atomic_step
               (icd_left ICD_SI ICD_SI') idx E).
Qed.

Lemma ic_left_lift_atomic_det_step idx E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     ▷ (∃ v2 σ2,
         ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> ICD_SI σ2 ∗
                          IC@{icd_right ICD_SI', 0}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_atomic_det_step
              (icd_left ICD_SI ICD_SI') idx E Φ e1).
Qed.

Lemma ic_left_lift_pure_det_step idx E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_left ICD_SI ICD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_det_step
            (icd_left ICD_SI ICD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_left_pure_step `{!Inhabited (state Λ)} idx E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n IC@{icd_left ICD_SI ICD_SI', idx}
    e2 @ E {{ v ; m | [x], Φ v (n + m) x }}
  ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (ic_pure_step (icd_left ICD_SI ICD_SI') idx); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply step_fupd_intro; first set_solver.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section ic_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → val Λ * nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_left_lift_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ ∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_left ICD_SI ICD_SI', idx}
                          e2 @ E {{ w; n | [x], Φ w (S n) x }}))
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by intros;
    iApply (ic_lift_head_step
              (icd_left ICD_SI ICD_SI') idx E Φ e1).
Qed.

Lemma ic_left_lift_pure_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_left ICD_SI ICD_SI', idx}
        e2 @ E {{ w; n| [x], Φ w (S n) x }})
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_head_step
            (icd_left ICD_SI ICD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_left_lift_atomic_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
     ▷ ∀ v2 σ2,
       ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (ICD_SI σ2 ∗ IC@{icd_right ICD_SI', 0}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
     ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by intros;
    iApply (ic_lift_atomic_head_step
              (icd_left ICD_SI ICD_SI') idx E Φ e1).
Qed.

Lemma ic_left_lift_pure_det_head_step idx E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ IC@{icd_left ICD_SI ICD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_det_head_step
            (icd_left ICD_SI ICD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

End ic_ectx_lifting.

Section ic_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → val Λ * nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_left_lift_head_step' idx E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
        ▷ (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (ICD_SI σ2 ∗ IC@{icd_left ICD_SI ICD_SI', idx}
                            e2 @ E {{ w; n | [x], Φ w (S n) x }})))
     ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_head_step'
              (icd_left ICD_SI ICD_SI') idx E Φ e1).
Qed.

Lemma ic_left_lift_pure_head_step' idx E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       IC@{icd_left ICD_SI ICD_SI', idx}
         e2 @ E {{ w; n | [x], Φ w (S n) x }})
     ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_head_step'
            (icd_left ICD_SI ICD_SI') idx E Φ e1); eauto.
   by iApply step_fupd_intro; first set_solver.
Qed.

Lemma ic_left_lift_atomic_head_step' idx E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 ={E, ∅}=∗
      ▷ (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
           (ICD_SI σ2 ∗ IC@{icd_right ICD_SI', 0}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }})))
    ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???).
  by iApply (ic_lift_atomic_head_step'
               (icd_left ICD_SI ICD_SI') idx E Φ e1).
Qed.

Lemma ic_left_lift_pure_det_head_step' idx E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  ▷ IC@{icd_left ICD_SI ICD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ IC@{icd_left ICD_SI ICD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_det_head_step'
            (icd_left ICD_SI ICD_SI') idx E Φ e1); eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

End ic_ectxi_lifting.

Section basic_soundness.
Context {Λ Σ} `{!invG Σ} (ICD_SI ICD_SI' : state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Lemma ic_left_adequacy_basic idx E e σ Φ :
  ICD_SI σ ∗ IC@{icd_left ICD_SI ICD_SI', idx} e @ E {{ λ v n x, Φ v n x.1 x.2 }} -∗
    ∀ (rd : Reds e σ),
      IC@{icd_right ICD_SI', nstps rd}
                          idx @ E {{ v; n, ICD_SI (end_state rd) ∗
                                          Φ (end_val rd) (nstps rd) v n }}.
Proof.
  iApply (ic_adequacy_basic
            (icd_left ICD_SI ICD_SI') idx E e σ (λ v n x, Φ v n x.1 x.2)).
Qed.

End basic_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ}
        {SI_data : Type} (ICD_SI : SI_data → state Λ → iProp Σ)
          {SI_data' : Type} (ICD_SI' : SI_data' → state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Program Instance left_Initialization
        SSI SSI' `{!InitData SSI} `{!InitData SSI'} e' σ' :
  Initialization
    (val Λ * nat)
    (λ x : invG_pack Σ (SI_data * SI_data'),
           icd_left (ICD_SI (PIG_cnt x).1) (ICD_SI' (PIG_cnt x).2))
    (λ x, @ICC_left Λ Σ _ (ICD_SI (PIG_cnt x).1) (ICD_SI' (PIG_cnt x).2))
    (λ _, e') :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x).1 ∗ SSI' (PIG_cnt x).2;
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_ICCM_soundness_arg := Reds e' σ';
  initialization_ICCM_soundness_laters n rd' := S ((nstps rd') + S n);
  initialization_modality_initializer x _ := ICD_SI' (PIG_cnt x).2 σ';
  initialization_ICCM_soundness_fun rd := (end_val rd, nstps rd);
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  intros; simpl.
  iApply init_data.
  apply (init_invGpack (λ x, SSI x.1 ∗ SSI' x.2))%I.
Qed.
Next Obligation.
Proof.
  iIntros (???? e' σ' P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  simpl.
  iIntros (???? e' σ' Hi P E n rd) "[[Hs HE] [Hσ' HP]]".
  iNext.
  rewrite /ICC_modality /ICD_modality /=.
  iDestruct (ic_right_adequacy_basic with "[Hσ' $HP]")
    as "HP"; eauto.
  iSpecialize ("HP" $! rd).
  rewrite uPred_fupd_eq /uPred_fupd_def /=.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  rewrite (plus_comm _ (S n))  -Nat.add_1_r -plus_assoc (plus_comm 1)
          plus_assoc bi.laterN_plus (plus_comm n) /=.
  iInduction (nstps rd + n) as [] "IH".
  { iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & ? & HP)".
    by iMod "HP". }
  simpl.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iNext.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  rewrite -bi.laterN_later /=.
  iMod "HP"; iMod "Hs"; iMod "HE".
  iApply ("IH" with "Hs HP HE").
Qed.

Lemma ic_left_adequacy SSI SSI' `{!InitData SSI} `{!InitData SSI'}
      E e σ (e' : expr Λ) σ' (Ψ : val Λ → nat → val Λ → nat → Prop) :
  (∀ (x : invG_pack Σ (SI_data * SI_data')),
      SSI (PIG_cnt x).1 ∗ SSI' (PIG_cnt x).2
          ⊢ |={⊤}=> (ICD_SI (PIG_cnt x).1 σ ∗ ICD_SI' (PIG_cnt x).2 σ' ∗
                  IC@{icd_left (ICD_SI (PIG_cnt x).1) (ICD_SI' (PIG_cnt x).2), e'}
                    e @ E {{ v ; n| w; k,  ⌜Ψ v n w k⌝ }}))
  → ∀ (rd : Reds e σ) (rd' : Reds e' σ'),
    Ψ (end_val rd) (@nstps Λ _ _ rd) (end_val rd') (@nstps Λ _ _ rd').
Proof.
  intros Hic rd rd'.
  by apply (ic_adequacy
              _ _ _ _ (left_Initialization SSI SSI' e' σ') E e σ
              (λ v n x, Ψ v n x.1 x.2) rd').
Qed.

End soundness.
