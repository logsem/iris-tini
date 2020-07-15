From iris.proofmode Require Import tactics.
From IC.if_convergent Require Import IC_adequacy.
From logrel_ifc.lambda_sec Require Export lang typing fundamental_binary.
From logrel_ifc.lambda_sec Require Import lattice.

Section soundness.

  Class lambdasecPreG Σ := LambdaSecPreG {
    lambdasec_preG_iris :> invPreG Σ;
    secGpre_gen_heapG_left :> gen_heapPreG loc val Σ;
    secGpre_gen_heapG_right :> gen_heapPreG loc val Σ;
  }.

  Context `{SecurityLattice label}.

  Definition secΣ : gFunctors :=
    #[invΣ; gen_heapΣ loc val; gen_heapΣ loc val].

  Definition SI_init Σ (x : gen_heapG loc val Σ) := gen_heap_ctx (hG := x) ∅.

  Instance SI_left_init_data `{!gen_heapPreG loc val Σ} : InitData (SI_init Σ).
  Proof. apply gen_heap_init. Qed.

  Definition SI Σ (x : gen_heapG loc val Σ) (σ : state) := gen_heap_ctx σ.

  Theorem soundness_semantic Σ `{lambdasecPreG Σ} e (b1 b2 : bool) (ℓ ℓ' : label)
          (rd  : Reds (e.[# (BoolV b1)/]) ∅)
          (rd' : Reds (e.[# (BoolV b2)/]) ∅)
          (flow1 : ℓ' ⋢ ζ)
          (flow2 : ℓ  ⊑ ζ) :
    (∀ (Hcnd : secG Σ), [ TBool @ (LLabel ℓ') ] ⊨ e ≤ₗ e : TBool @ (LLabel ℓ)) →
    end_val rd = end_val rd'.
  Proof.
    intros Hlog.
    eapply (ic_left_adequacy
              (SI Σ) (SI Σ) (SI_init Σ) (SI_init Σ) _ _ _ _ _ (λ x _ y _, x = y)).
    iIntros ([? [leftG rightG]]).
    rewrite /SI_init /SI /=.
    iIntros "[Hl Hr]".
    iModIntro. iFrame.
    iApply (ic_wand_r with "[-]"); iSplitL.
    { iApply (Hlog (SecG _ _ leftG rightG) [] [] [(BoolV b1, BoolV b2)] with "[]").
      iSplit; first rewrite /env_coherent //.
      iApply interp_env_cons.
      iSplit; last by iApply interp_env_nil.
      rewrite interp_sec_def interp_bool_def /=.
      rewrite bool_decide_eq_false_2 //.
      rewrite !interp_un_sec_def !interp_un_bool_def; auto. }
    iIntros (? ? ?) "H /=".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
    by iDestruct "H" as (c1 c2) "(->&->&->)".
  Qed.

  Theorem soundness_tini (e : expr) v1 v2 v1' v2' ℓ ℓ' :
    ℓ' ⋢ ζ →
    ℓ  ⊑ ζ →
    [TBool @ (LLabel ℓ')] # (LLabel ℓ) ⊢ₜ e : TBool @ (LLabel ℓ) →
    [] # (LLabel ℓ) ⊢ₜ #v1 : TBool @ (LLabel ℓ') →
    [] # (LLabel ℓ) ⊢ₜ #v2 : TBool @ (LLabel ℓ') →
    ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) ∧
     (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) →
    v1' = v2'.
  Proof.
    intros Hflow1 Hflow2 Htpe Htp1 Htp2 [Hrd1 Hrd2].
    destruct (bool_val_typed _ _ _ _ v1 _ Htp1);
      eauto using to_of_val; [simplify_eq].
    destruct (bool_val_typed _ _ _ _ v2 _ Htp2);
      eauto using to_of_val; [simplify_eq].
    destruct Hrd1 as [σ1 Hrd1].
    destruct Hrd2 as [σ2 Hrd2].
    destruct (rtc_nsteps _ _ Hrd1) as [n1 Hrd1'].
    destruct (rtc_nsteps _ _ Hrd2) as [n2 Hrd2'].
    assert (lambdasecPreG #[secΣ]) as HPG.
    { constructor; apply _. }
     set (Hrd1'' := {| reds := Hrd1' |}).
    set (Hrd2'' := {| reds := Hrd2' |}).
    apply (soundness_semantic #[secΣ] _ _ _ ℓ ℓ' Hrd1'' Hrd2''); [done..|].
    intros ?.
    by eapply binary_fundamental.
  Qed.

End soundness.

Section soundness_tp.

  Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
  Notation H := (LLabel H).
  Notation L := (LLabel L).

  Theorem soundness_tini_tp (e : expr) v1 v2 v1' v2' :
    [TBool @ H] # L ⊢ₜ e : TBool @ L →
    [] # L ⊢ₜ #v1 : TBool @ H →
    [] # L ⊢ₜ #v2 : TBool @ H →
    ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) ∧
     (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) →
    v1' = v2'.
  Proof. by apply soundness_tini. Qed.

End soundness_tp.
