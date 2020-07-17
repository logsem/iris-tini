From iris.base_logic Require Import wsat fancy_updates.
From iris.proofmode Require Import tactics.

Class invG_pack Σ A := PackInvG {PIG_invG :> invG Σ; PIG_cnt : A}.

Arguments PackInvG {_ _ _} _.
Arguments PIG_cnt {_ _} _.

Class InitData {Σ A} (SSI : A → iProp Σ) := init_data : ⊢ |==> ∃ x, SSI x.

Arguments init_data {_ _} _ {_}.

Instance InitData_sep
        {Σ A B} (SSI : A → iProp Σ) (SSI' : B → iProp Σ) `{!InitData SSI} `{!InitData SSI'} :
  InitData (λ x : A * B, SSI x.1 ∗ SSI' x.2)%I.
Proof.
  rewrite /InitData.
  iMod (init_data SSI) as (a) "Ha".
  iMod (init_data SSI') as (b) "Hb".
  iModIntro.
  iExists (a, b); iFrame.
Qed.

Instance init_invGpack
        {Σ A} (SSI : A → iProp Σ) `{!invPreG Σ} `{!InitData SSI} :
  InitData (λ x : invG_pack Σ A, (wsat ∗ ownE ⊤) ∗ SSI (PIG_cnt x))%I.
Proof.
  rewrite /InitData.
  iMod wsat_alloc as (?) "[? ?]".
  iMod init_data as (a) "Ha".
  iModIntro.
  iExists (PackInvG a); iFrame.
Qed.

Section Lemmas.
  Context {Σ} `{!invG Σ}.

  Implicit Types P Q : iProp Σ.

  Lemma step_fupdN_intro k E P : P -∗ |={E}[∅]▷=>^k P.
  Proof.
    iIntros "H".
    iInduction k as [] "IH"; simpl; first done.
    iApply step_fupd_intro; first set_solver.
    by iNext; iApply "IH".
  Qed.

  Lemma step_fupdN_mask_mono k E1 E2 P :
    E1 ⊆ E2 → (|={E1}[∅]▷=>^k P) -∗ |={E2}[∅]▷=>^k P.
  Proof.
    iIntros (?) "H".
    iInduction k as [] "IH"; simpl; first done.
    iMod (fupd_intro_mask' E2 E1) as "Hcl"; first done.
    iMod "H"; iModIntro; iNext; iMod "H"; iMod "Hcl" as "_".
    iModIntro.
    by iApply "IH".
  Qed.

  Lemma step_fupdN_plus k k' E E' (P : iProp Σ) :
    (|={E}[E']▷=>^k (|={E}[E']▷=>^k' P)) ⊣⊢ |={E}[E']▷=>^(k + k') P.
  Proof.
    iInduction k as [] "IHk" forall (k' P); simpl.
    - iInduction k' as [] "IHk'"; simpl; first by iSplit; auto.
      iSplit; iIntros "H".
      + iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
        by iApply "IHk'".
      + iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
        by iApply "IHk'".
    - iInduction k' as [] "IHk'"; simpl.
      + iSplit; iIntros "H".
        * iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
          by iApply "IHk".
        * iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
          by iApply ("IHk" $! 0).
      + iSplit; iIntros "H".
        * iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
          by iApply "IHk".
        * iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
          by iApply ("IHk" $! (S k')).
  Qed.

  Class StepFupdElimCond k k' := step_fupd_elim_cond : k ≤ k'.

  Global Instance elim_modal_steps_fupd p E E' P Q k k':
    StepFupdElimCond k' k →
    ElimModal True p false (|={E}[E']▷=>^k' P) P (|={E}[E']▷=>^k Q)
              (|={E}[E']▷=>^(k - k') Q).
  Proof.
    rewrite /StepFupdElimCond.
    iIntros (Hk _) "[HP HQ]".
    rewrite -{2}(Nat.sub_add k' k) // plus_comm -step_fupdN_plus.
    iDestruct (bi.intuitionistically_if_elim with "HP") as "HP".
    iInduction k' as [|k'] "IH" forall (k Hk); simpl; first by iApply "HQ".
    iMod "HP"; iModIntro; iNext; iMod "HP"; iModIntro.
    destruct k; simpl; first lia.
    iApply ("IH" with "[] HQ HP"); auto with lia.
  Qed.

  Global Instance elim_modal_fupd_steps_fupd_fupd p E E' P Q k :
    ElimModal True p false (|={E}=> P) P (|={E}[E']▷=>^k |={E}=> Q)
              (|={E}[E']▷=>^k |={E}=> Q).
  Proof.
    iIntros (_) "[HP HQ]".
    iDestruct (bi.intuitionistically_if_elim with "HP") as "HP".
    destruct k; simpl.
    - by iMod "HP"; iApply "HQ".
    - by iMod "HP"; iApply "HQ".
  Qed.

End Lemmas.

Hint Extern 1 (StepFupdElimCond _ _) =>
  rewrite /StepFupdElimCond; solve [done|lia] : typeclass_instances.
