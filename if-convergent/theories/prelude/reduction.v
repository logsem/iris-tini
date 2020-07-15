From iris.program_logic Require Import language.
From stdpp Require Import relations.

Notation pstep' l :=
  (λ x1 x2, @prim_step l (fst x1) (snd x1) [] (fst x2) (snd x2) []).
Notation pstep := (λ x1 x2, prim_step (fst x1) (snd x1) [] (fst x2) (snd x2) []).

Lemma nsteps_val l k v σ e' σ':
  nsteps pstep k (of_val v, σ) (e', σ') → k = 0 ∧ e' = (@of_val l v) ∧ σ = σ'.
Proof.
  inversion 1 as [|Hs1 Hs2 Hs3 Hs4 Hs5 Hs6]; simpl in *; subst; first done.
  by apply val_stuck in Hs5; rewrite to_of_val in Hs5.
Qed.

Lemma nsteps_atomic a l k e σ e' σ' (Hat : Atomic a e):
  nsteps (pstep' l) k (e, σ) (e', σ') → k ≤ 1.
Proof.
  intros Hstp.
  inversion Hstp as [|j Hs2 [e'' σ''] Hs4 Hs5 Hs6]; simpl in *; simplify_eq;
    first by eauto.
  specialize (Hat _ _ _ _ _ Hs5).
  destruct a.
  - destruct Hat as [? ?%of_to_val]; simplify_eq.
    by apply nsteps_val in Hs6; destruct Hs6 as [? [? ?]]; simplify_eq.
  - inversion Hs6 as [|j' Hs2' [e''' σ'''] Hs4' Hs5' Hs6'];
      simpl in *; simplify_eq; first by eauto.
    by specialize (Hat _ _ _ _ Hs5').
Qed.

Lemma nsteps_bind {Λ} K `{!@LanguageCtx Λ K} {n e σ v σ'} :
  nsteps pstep n (K e, σ) (of_val v, σ') →
  ∃ k σ'' w, k ≤ n ∧ nsteps pstep k (e, σ) (of_val w, σ'') ∧
             nsteps pstep (n - k) (K (of_val w), σ'') (of_val v, σ').
Proof.
  destruct (to_val e) as [w|] eqn:?;
    first (subst;  apply of_to_val in Heqo as <-).
  { exists 0, σ, w; replace (n-0) with n by lia;
      repeat split; [|constructor|]; auto with lia. }
  revert e σ Heqo; induction n => e σ Heqo Hr.
  - inversion Hr as [Hs1 Hs2 Hs3 Hs4|]; subst.
    assert (Hkv : to_val (K e) = None) by by rewrite fill_not_val.
    by rewrite Hs4 to_of_val in Hkv.
  - inversion Hr as [|Hs1 Hs2 [e2 σ2] Hs4 Hs5 Hs6]; subst.
    simpl in *.
    apply fill_step_inv in Hs5; trivial.
    destruct Hs5 as [e2' [Hs51 Hs5]]; subst.
    destruct (to_val e2') as [w'|] eqn:Heqo';
      first (subst;  apply of_to_val in Heqo' as <-).
    { exists 1, σ2, w'.
      simpl; replace (n-0) with n by lia.
      repeat split; auto with lia.
      eapply (nsteps_l _ _ _ (_, _) (_, _)); simpl; eauto.
      constructor. }
    destruct (IHn e2' σ2 Heqo' Hs6) as (k & σ'' & z & Hle & Hstp1 & Hstp2).
    exists (S k), σ'', z; repeat split; auto with lia.
    eapply (nsteps_l _ _ _ (_, _) (_, _)); simpl; eauto.
Qed.

Lemma nsteps_bind' {Λ} K `{!@LanguageCtx Λ K} {n n' e σ v σ' e'' σ''} :
  nsteps pstep n (e, σ) (of_val v, σ') →
  nsteps pstep n' (K (of_val v), σ') (e'', σ'') →
  nsteps pstep (n + n') (K e, σ) (e'', σ'').
Proof.
  revert n' e σ v σ' e'' σ''.
  induction n => n' e σ v σ' e'' σ''.
  { by intros H1; inversion H1; subst; simpl in *. }
  intros H1 H2; inversion H1 as [|Hs1 Hs2 [e2 σ2] Hs4 Hs5 Hs6];
    subst; simpl in *.
  eapply (nsteps_l _ _ _ (_, _) (_, _)); simpl; eauto.
  by apply fill_step.
Qed.

Lemma nsteps_ctx {Λ} K `{!@LanguageCtx Λ K} {n e σ e' σ'} :
  nsteps pstep n (e, σ) (e', σ') →
  nsteps pstep n (K e, σ) (K e', σ').
Proof.
  revert e σ e' σ'; induction n => e σ e' σ'; inversion 1 as [[? ?]|? ? [? ?]]; subst.
  - econstructor.
  - eapply (nsteps_l _ _ _ (_, _) (_, _)); simpl in *; eauto.
    eapply fill_step; eauto.
Qed.

Lemma rtc_ctx {Λ} K `{!@LanguageCtx Λ K} {e σ e' σ'} :
  rtc pstep (e, σ) (e', σ') →
  rtc pstep (K e, σ) (K e', σ').
Proof.
  move=> Hstp. apply rtc_nsteps in Hstp as [n Hstp]. apply (nsteps_rtc n).
  by apply nsteps_ctx.
Qed.

Definition nf_reducible {l : language} e σ := ∃ e' σ', @prim_step l e σ [] e' σ' [].
Lemma nf_red_red {l} e σ : nf_reducible e σ → @reducible l e σ.
Proof. destruct 1 as [? [? ?]]; eexists; eauto. Qed.

From iris.program_logic Require ectx_language.

Section nf_head_reducible.
  Context {Λ : ectx_language.ectxLanguage}.

  Definition nf_head_reducible e σ :=
    ∃ e' σ', @ectx_language.head_step Λ e σ [] e' σ' [].
  Lemma nf_head_red_head_red e σ :
    nf_head_reducible e σ → ectx_language.head_reducible e σ.
  Proof. destruct 1 as [? [? ?]]; eexists; eauto. Qed.

  Lemma nf_head_reducible_nf_reducible e σ :
    nf_head_reducible e σ → @nf_reducible (ectx_language.ectx_lang _) e σ.
  Proof.
    destruct 1 as [? [? ?]]; do 2 eexists.
    eapply ectx_language.head_prim_step; eauto.
  Qed.

End nf_head_reducible.

From iris.program_logic Require ectxi_language.

Section step_by_val_strong.
  Context {Λ : ectxi_language.ectxiLanguage}.

  Lemma app_neq_self {A} (l l' : list A) : l ++ l' = l' → l = [].
  Proof.
    revert l; induction l' using rev_ind; intros l Heq.
    - by destruct l; inversion Heq.
    - apply IHl'. apply (inj (λ k, app k [x])).
      by rewrite -assoc.
  Qed.

  Lemma step_by_val_strong K K' e1 e1' σ1 e2 σ2 efs σ1' e2' σ2' efs' :
    ectxi_language.fill K e1 = ectxi_language.fill K' e1' →
    @ectx_language.head_step (ectxi_language.ectxi_lang_ectx Λ) e1 σ1 [] e2 σ2 efs →
    @ectx_language.head_step (ectxi_language.ectxi_lang_ectx Λ) e1' σ1' [] e2' σ2' efs' → K = K'.
  Proof.
    intros HK Hh1 Hh2.
    edestruct (@ectx_language.step_by_val (ectxi_language.ectxi_lang_ectx Λ))
      as [K3 HK3]; eauto.
    { eapply (ectxi_language.mixin_val_stuck
                _ _ _ _ (ectxi_language.ectxi_language_mixin Λ)); eauto. }
    symmetry in HK.
    edestruct (@ectx_language.step_by_val (ectxi_language.ectxi_lang_ectx Λ))
      as [K4 HK4]; eauto.
    { eapply (ectxi_language.mixin_val_stuck
                _ _ _ _ (ectxi_language.ectxi_language_mixin Λ)); eauto. }
    rewrite HK3 in HK4.
    simpl in *.
    rewrite assoc in HK4.
    symmetry in HK4; eapply app_neq_self, app_nil in HK4.
    by destruct HK4 as [_ ->].
  Qed.

End step_by_val_strong.
