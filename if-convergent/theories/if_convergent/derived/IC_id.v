From iris.proofmode Require Import tactics classes.
From IC.if_convergent Require Import IC IC_adequacy IC_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ic_id.
  Context {Λ Σ} (ICD_SI : state Λ → iProp Σ).

  Definition icd_id : ICData Λ Σ :=
    {| ICD_state_interp := ICD_SI;
       ICD_Extra := [Prod];
       ICD_modality_index := [Prod];
       ICD_modality_bind_condition idx idx' f Ξ := Ξ = λ _, id;
       ICD_modality idx E n Φ := Φ tt |}.

  Global Instance ICC_id : ICC icd_id.
  Proof.
    split.
    - by intros idx E m n P Q HPQ; simpl.
    - intros idx E1 E2 n P Q ?; simpl. by iIntros "H ?"; iApply "H".
    - by intros P E n.
    - by intros idx E n m P ? ? ? ->; simpl.
  Qed.

  Global Program Instance IC_id_SplitForStep idx : ICMSplitForStep icd_id idx :=
    {|
      ICM_split_for_step_M1 E P := P;
      ICM_split_for_step_M2 E P := P;
    |}%I.
  Next Obligation.
  Proof.
    by iIntros (idx [] E P) "HP /="; rewrite /ICC_modality /ICD_modality /=.
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iApply "HPQ".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iApply "HPQ".
  Qed.

  Lemma ic_id_bind K `{!LanguageCtx K} idx E e Φ :
    IC@{icd_id, idx} e @ E {{ v; m,
      IC@{icd_id, idx} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ IC@{icd_id, idx} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros "?".
    by iApply (@ic_bind _ _ _ ICC_id K _ _ _ _ (λ _, id)).
  Qed.

End ic_id.

Section lifting.

Context {Λ Σ} (ICD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_id_lift_step  E Φ e1 :
  to_val e1 = None →
    (∀ σ1, ICD_SI σ1 -∗
     ∀ e2 σ2,
       ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
        (ICD_SI σ2 ∗ IC@{icd_id ICD_SI}
                e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (ic_lift_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_step  E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_id ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  intros.
  by iApply (ic_lift_pure_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_atomic_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 -∗
     ∀ v2 σ2,
       ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
        -∗ (ICD_SI σ2 ∗ Φ v2 1))
⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (ic_lift_atomic_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1); simpl.
Qed.

Lemma ic_id_lift_atomic_det_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, ICD_SI σ1 -∗
     ∃ v2 σ2,
       ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                   σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                   ICD_SI σ2 ∗ Φ v2 1)
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_atomic_det_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_det_step  E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  IC@{icd_id ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (ic_lift_pure_det_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
Qed.

Lemma ic_id_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  IC@{icd_id ICD_SI} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (ic_pure_step (icd_id ICD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section ic_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} (ICD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_id_lift_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, ICD_SI σ1 -∗
     ∀ e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
        (ICD_SI σ2 ∗ IC@{icd_id ICD_SI} e2 @ E {{ w; n, Φ w (S n) }}))
     ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (ic_lift_head_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_id ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  intros.
   by iApply (ic_lift_pure_head_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_atomic_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 -∗
     ∀ v2 σ2,
       ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ -∗
        (ICD_SI σ2 ∗ Φ v2 1))
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (ic_lift_atomic_head_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_det_head_step  E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  IC@{icd_id ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (ic_lift_pure_det_head_step (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
Qed.

End ic_ectx_lifting.

Section ic_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} (ICD_SI : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent ICC_state_interp ICD_state_interp ICC_modality.

Lemma ic_id_lift_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, ICD_SI σ1 -∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             (ICD_SI σ2 ∗ IC@{icd_id ICD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (ic_lift_head_step' (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      IC@{icd_id ICD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_head_step' (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1);
    eauto.
Qed.

Lemma ic_id_lift_atomic_head_step'  E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, ICD_SI σ1 -∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ -∗ (ICD_SI σ2 ∗ Φ v2 1)))
    ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (ic_lift_atomic_head_step' (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma ic_id_lift_pure_det_head_step'  E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  IC@{icd_id ICD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ IC@{icd_id ICD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (ic_lift_pure_det_head_step' (icd_id ICD_SI) _ E (λ v n _, Φ v n) e1);
    eauto.
Qed.

End ic_ectxi_lifting.

Section basic_soundness.
Context {Λ Σ} (ICD_SI : state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Lemma ic_id_adequacy_basic  E e σ Φ :
  ICD_SI σ ∗ IC@{icd_id ICD_SI} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ), ICD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (ic_adequacy_basic (icd_id ICD_SI) _ E e σ (λ v n _, Φ v n)).
Qed.

End basic_soundness.

Section soundness.
Context {Λ Σ} {SI_data : Type} (ICD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent ICC_state_interp ICC_modality.

Program Instance id_Initialization SSI `{!InitData SSI}:
  Initialization
    unit
    (λ x : SI_data, icd_id (ICD_SI x))
    (λ x, ICC_id (ICD_SI x))
    (λ _, tt) :=
{|
  initialization_modality Hi P := |==> P;
  initialization_seed_for_modality _ := True;
  initialization_seed_for_state_interp x := SSI x;
  initialization_residue _ := True;
  initialization_elim_laters := 0;
  initialization_ICCM_soundness_arg := unit;
  initialization_ICCM_soundness_laters _ _ := 0;
  initialization_modality_initializer _ _ := True;
  initialization_ICCM_soundness_fun _ := tt;
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  iIntros.
  iMod init_data as (?) "?".
  iModIntro; iExists _; iFrame.
Qed.
Next Obligation.
Proof.
  by iIntros (?? P Hi) "_ >HP"; iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (?? Hi P E n _) "[_ [_ HP]]".
  by rewrite /ICC_modality /ICD_modality /=.
Qed.

Lemma ic_id_adequacy SSI `{!InitData SSI} E e σ (Ψ : val Λ → nat → Prop):
  (∀ (x : SI_data),
  (SSI x ⊢ |==> (ICD_SI x σ ∗ IC@{icd_id (ICD_SI x)} e @ E {{ v ; n, ⌜Ψ v n⌝ }})))
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (ic_adequacy _ _ _ _ (id_Initialization SSI) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "?"; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
