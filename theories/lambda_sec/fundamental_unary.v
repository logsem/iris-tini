From iris.algebra Require Import list.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Import lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.
From iris.proofmode Require Import tactics ltac_tactics.
From mwp.mwp_modalities Require Export mwp_step_fupd.
From logrel_ifc.lambda_sec Require Export lang rules_unary typing logrel_label logrel_unary.

Section unary_log_def.
  Context `{secG_un Σ}.
  Context `{SecurityLattice label}.

  Definition un_log_related (Γ : list sectype) (e : expr) (τ : sectype) (pc : label_term) :=
    ∀ Δ ρ vs,
      env_Persistent Δ →
      ⌊ Γ ⌋* Δ ρ vs ⊢ ⌊ τ ⌋ₑ Δ ρ pc e.[env_subst vs].

End unary_log_def.

Notation "Γ # pc ⊨ᵤ e : τ" :=
  (un_log_related Γ e τ pc) (at level 74, e, τ at next level).

Section fundamental.
  Context `{secG_un Σ}.
  Context `{SecurityLattice label}.

  Notation D := (val -d> iPropO Σ).
  Notation lty := (listO D -n> listO labelO -d> D).

  Local Tactic Notation "smart_mwp_bind" uconstr(ctx) ident(v) ident(n)
        ident(x) constr(Hv) constr(Hp) :=
    iApply (mwp_step_fupd_bind SI (fill [ctx]));
    iApply (mwp_wand_r with "[-]"); iSplitL; [iApply Hp; trivial|]; cbn;
    iIntros (v n x) Hv.

  Lemma interp_un_secsubtype τ1 τ2 Δ ρ v :
    env_Persistent Δ →
    τ1 <:ₛ τ2 → ⌊ τ1 ⌋ₛ Δ ρ v -∗ ⌊ τ2 ⌋ₛ Δ ρ v.
  Proof.
    move=> Henv Hsub. move: Δ Henv ρ v.
    elim Hsub using secsubtype_mut
      with (P := (λ t1 t2 Hsub, ∀ Δ ρ v, env_Persistent Δ →
        ⌊ t1 ⌋ Δ ρ v -∗ ⌊ t2 ⌋ Δ ρ v)); try done.
    - iIntros (???? Hsub1 ? Hsub2 ????) "Ht1 /=".
      by iApply Hsub2; iApply Hsub1.
    - iIntros (??????? Hsub1 ? Hsub2 ??).
      iIntros (???). rewrite !interp_un_arrow_def.
      iIntros "#Hsub !>" (?) "#Hτ1' %" . iApply mwp_wand_r; iSplitL.
      + iApply "Hsub"; [by iApply Hsub1|]. iPureIntro.
        by eapply ord_neg_left; [apply interp_label_flowsto|].
      + iIntros (???). by iApply Hsub2.
    - iIntros (?????? IH ????). rewrite !interp_un_tforall_def.
      iIntros "#Hsub !>" (???). iApply (mwp_wand_r (mwpd_step_fupd SI)); iSplitL.
      + iApply "Hsub"; try done. iPureIntro.
        by eapply ord_neg_left; [apply interp_label_flowsto|].
      + iIntros (???) "?". by iApply IH.
    - iIntros (?????? IH ????). rewrite !interp_un_tlforall_def.
      iIntros "#Hsub !>" (??). iApply mwp_wand_r; iSplitL.
      + iApply "Hsub"; try done. iPureIntro.
        by eapply ord_neg_left; [apply interp_label_flowsto|].
      + iIntros (???) "?". by iApply IH.
    - iIntros (????? IH1 ? IH2 ????). rewrite !interp_un_prod_def.
      iDestruct 1 as (? ?) "[-> [Hτ1 Hτ2]]".
      iDestruct (IH1 with "Hτ1") as "Hτ1'".
      iDestruct (IH2 with "Hτ2") as "Hτ2'".
      eauto.
    - iIntros (????? IH1 ? IH2 ????). rewrite !interp_un_sum_def.
      iDestruct 1 as "[Hτ0 | Hτ1]"; [iLeft | iRight].
      + iDestruct "Hτ0" as (?) "[-> Hτ0]".
        iDestruct (IH1 with "Hτ0") as "?"; eauto.
      + iDestruct "Hτ1" as (?) "[-> Hτ1]".
        iDestruct (IH2 with "Hτ1") as "?"; eauto.
    - iIntros (??? IH ????). rewrite !interp_un_rec_def.
      rewrite !fixpoint_interp_un_rec1_eq /interp_un_rec1 /=.
      iDestruct 1 as (?) "[-> #Hτ0]".
      iModIntro. iExists _. iSplit; [done|]. iModIntro.
      replace (fixpoint _) with (⌊ TRec τ0 ⌋ Δ ρ); [|done].
      replace (fixpoint _) with (⌊ TRec τ3 ⌋ Δ ρ); [|done].
      iApply (interp_un_sec_type_subst_up _ []); [done|].
      iDestruct ((interp_un_sec_type_subst_up _ []) with "Hτ0") as "H"; [done|].
      asimpl. by iApply IH.
    - iIntros (?????? IH ????).
      rewrite !interp_un_sec_def. by iApply IH.
  Qed.

  Lemma un_log_related_unit Γ pc :
    Γ # pc ⊨ᵤ Unit : TUnit @ ⊥ₛ.
  Proof.
    iIntros (????) "? %".
    iApply mwp_value; umods.
    rewrite interp_un_unit_def //.
  Qed.

  Lemma un_log_related_bool Γ pc b :
    Γ # pc ⊨ᵤ Bool b : TBool @ ⊥ₛ.
  Proof.
    iIntros (????) "? %".
    iApply mwp_value; umods.
    iModIntro. by iExists _.
  Qed.

  Lemma un_log_related_nat Γ pc n :
    Γ # pc ⊨ᵤ Nat n : TNat @ ⊥ₛ.
  Proof.
    iIntros (????) "? %".
    iApply mwp_value; umods.
    iModIntro. by iExists _.
  Qed.

  Lemma un_log_related_var Γ pc x τ :
    Γ !! x = Some τ → Γ # pc ⊨ᵤ Var x : τ.
  Proof.
    iIntros (?????) "#? %".
    iDestruct (interp_un_env_Some_l with "[]") as (v) "[% H] /="; [eauto|].
    erewrite !env_subst_lookup; eauto.
    by iApply (mwp_value (mwpd_step_fupd SI)); umods.
  Qed.

  Lemma un_log_related_lam Γ pc ℓₑ e τ1 τ2
        (IHtyped : τ1 :: Γ # ℓₑ ⊨ᵤ e : τ2)
    : Γ # pc ⊨ᵤ Lam e : TArrow ℓₑ τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    iDestruct (interp_un_env_length with "[]") as %Hlen; [done|].
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_arrow_def.
    do 2 iModIntro.
    iIntros (w) "#Hw %".
    iDestruct (interp_un_env_cons with "[$]") as "Hctx'".
    iDestruct ((IHtyped _ _ (w :: vs)) with "[$]") as "H".
    iApply mwp_step_fupd_pure_step; [done|]. cbn.
    assert (e.[# w .: env_subst vs] =
            e.[up (env_subst vs)].[# w/]) as -> by autosubst.
    by iApply "H".
  Qed.

  Lemma un_log_related_binop Γ pc op e1 e2 ℓ1 ℓ2
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : TNat @ ℓ1)
        (IHtyped2 : Γ # pc ⊨ᵤ e2 : TNat @ ℓ2)
    : Γ # pc ⊨ᵤ BinOp op e1 e2 : (binop_type op) @ ℓ1 ⊔ₛ ℓ2.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (BinOpLCtx _ _) v k x "#Hv" IHtyped1.
    smart_mwp_bind (BinOpRCtx _ _) w m y "#Hw" IHtyped2.
    rewrite !interp_un_nat_def.
    iDestruct "Hv" as (b) "->"; iDestruct "Hw" as (b') "->".
    iApply mwp_step_fupd_pure_step; [done|].
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    destruct op;
      rewrite /binop_type ?interp_un_nat_def ?interp_un_bool_def /=;
        try case_bool_decide; eauto.
  Qed.

  Lemma un_log_related_app Γ pc e1 e2 τ1 τ2 ℓₑ ℓ
        (Hflow : pc ⊔ₛ ℓ ⊑ₛ ℓₑ)
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : TArrow ℓₑ τ1 τ2 @ ℓ)
        (IHtyped2 : Γ # pc ⊨ᵤ e2 : τ1)
    : Γ # pc ⊨ᵤ App e1 e2 : τ2.
  Proof.
    iIntros (? ρ ??) "#? %".
    smart_mwp_bind (AppLCtx (e2.[env_subst vs])) v k x "#Hv" IHtyped1.
    smart_mwp_bind (AppRCtx v) w m y "#Hw" IHtyped2.
    rewrite interp_un_arrow_def.
    iApply ("Hv" with "Hw"). iPureIntro.
    move: Hflow=> /interp_label_flowsto /= /(_ ρ) Hflow.
    apply join_ord_inv in Hflow as [? ?].
    by eapply (ord_neg_left (⌊ pc ⌋ₗ _)).
  Qed.

  Lemma un_log_related_letin Γ pc e1 e2 τ1 τ2
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : τ1)
        (IHtyped2 : τ1 :: Γ # pc ⊨ᵤ e2 : τ2)
    : Γ # pc ⊨ᵤ LetIn e1 e2 : τ2.
  Proof.
    iIntros (????) "#? % /=".
    smart_mwp_bind (LetInCtx _) v k x "#Hv" IHtyped1.
    iApply mwp_step_fupd_pure_step; [done|].
    iModIntro.
    assert (e2.[up (env_subst vs)].[# v/] =
            e2.[# v .: env_subst vs]) as Heq by autosubst.
    rewrite Heq.
    iApply (IHtyped2 _ _ (v :: vs)); [|done].
    iApply interp_un_env_cons. auto.
  Qed.

  Lemma un_log_related_seq Γ pc e1 e2 τ1 τ2
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : τ1)
        (IHtyped2 : Γ # pc ⊨ᵤ e2 : τ2)
    : Γ # pc ⊨ᵤ Seq e1 e2 : τ2.
  Proof.
    iIntros (????) "#? % /=".
    smart_mwp_bind (SeqCtx _) v k x "#Hv" IHtyped1.
    iApply mwp_step_fupd_pure_step; [done|].
    by iApply IHtyped2.
  Qed.

  Lemma un_log_related_if Γ pc e e1 e2 τ ℓ
          (IHtyped1 : Γ # pc ⊨ᵤ e : TBool @ ℓ)
          (IHtyped2 : Γ # pc ⊔ₛ ℓ ⊨ᵤ e1 : τ)
          (IHtyped3 : Γ # pc ⊔ₛ ℓ ⊨ᵤ e2 : τ)
    : Γ # pc ⊨ᵤ If e e1 e2 : τ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (IfCtx e1.[env_subst vs] e2.[env_subst vs]) v k x "#Hv" IHtyped1.
    rewrite interp_un_bool_def. iDestruct "Hv" as (b) "%"; iSimplifyEq.
    destruct b; iApply mwp_step_fupd_pure_step; try done; iNext.
    - iApply IHtyped2; [done|]. iPureIntro.
      eapply (ord_neg_left (⌊ pc ⌋ₗ _)); [|done].
      by apply ord_join_left.
    - iApply IHtyped3; [done|]. iPureIntro.
      eapply (ord_neg_left (⌊ pc ⌋ₗ _)); [|done].
      by apply ord_join_left.
  Qed.

  Lemma un_log_related_pair Γ pc e1 e2 τ1 τ2
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : τ1)
        (IHtyped2 : Γ # pc ⊨ᵤ e2 : τ2)
    : Γ # pc ⊨ᵤ Pair e1 e2 : TProd τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (PairLCtx _) v1 n1 x1 "#Hv1" IHtyped1.
    smart_mwp_bind (PairRCtx _) v2 n2 x2 "#Hv2" IHtyped2.
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    iModIntro. rewrite interp_un_prod_def. eauto.
  Qed.

  Lemma un_log_related_proj1 Γ pc e τ1 τ2 ℓ
        (IHtyped : Γ # pc ⊨ᵤ e : TProd τ1 τ2 @ ℓ)
    : Γ # pc ⊨ᵤ Proj1 e : τ1.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind Proj1Ctx v k x "#Hv" IHtyped.
    rewrite interp_un_prod_def.
    iDestruct "Hv" as (v1 v2) "[-> [Hv1 Hv2]]"; iSimplifyEq.
    iApply mwp_step_fupd_pure_step; [done|].
    iNext. iApply (mwp_value (mwpd_step_fupd SI)); umods.
    by iApply "Hv1".
  Qed.

  Lemma un_log_related_proj2 Γ pc e τ1 τ2 ℓ
        (IHtyped : Γ # pc ⊨ᵤ e : TProd τ1 τ2 @ ℓ)
    : Γ # pc ⊨ᵤ Proj2 e : τ2.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind Proj2Ctx v k x "#Hv" IHtyped.
    rewrite interp_un_prod_def.
    iDestruct "Hv" as (v1 v2) "[-> [Hv1 Hv2]]"; iSimplifyEq.
    iApply mwp_step_fupd_pure_step; [done|].
    iNext. iApply (mwp_value (mwpd_step_fupd SI)); umods.
    by iApply "Hv2".
  Qed.

  Lemma un_log_related_inl Γ pc e τ1 τ2
        (IHtyped : Γ # pc ⊨ᵤ e : τ1)
    : Γ # pc ⊨ᵤ InjL e : TSum τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind InjLCtx v m x "#Hv" IHtyped.
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_sum_def. eauto.
  Qed.

  Lemma un_log_related_inr Γ pc e τ1 τ2
        (IHtyped : Γ # pc ⊨ᵤ e : τ2)
    : Γ # pc ⊨ᵤ InjR e : TSum τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind InjRCtx v m x "#Hv" IHtyped.
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_sum_def. eauto.
  Qed.

  Lemma un_log_related_case Γ pc e e1 e2 τ τ1 τ2 ℓ
          (IHtyped1 : Γ # pc ⊨ᵤ e : TSum τ1 τ2 @ ℓ)
          (IHtyped2 : τ1 :: Γ # pc ⊔ₛ ℓ ⊨ᵤ e1 : τ)
          (IHtyped3 : τ2 :: Γ # pc ⊔ₛ ℓ ⊨ᵤ e2 : τ)
    : Γ # pc ⊨ᵤ Case e e1 e2 : τ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (CaseCtx _ _) v k x "#Hv" IHtyped1.
    rewrite interp_un_sum_def.
    iDestruct "Hv" as "[Hw1 | Hw2]".
    - iDestruct "Hw1" as (w) "[-> Hw1]".
      iApply mwp_step_fupd_pure_step; [done|].
      assert (e1.[up (env_subst vs)].[# w/] =
              e1.[# w .: env_subst vs]) as Heq by autosubst.
      rewrite -/of_val Heq. iModIntro.
      iApply (IHtyped2 _ _ (w :: vs)).
      { iApply interp_un_env_cons. auto. }
      iPureIntro.
      eapply ord_neg_left; [|done]. by apply ord_join_left.
    - iDestruct "Hw2" as (w) "[-> Hw1]".
      iApply mwp_step_fupd_pure_step; [done|].
      assert (e2.[up (env_subst vs)].[# w/] =
              e2.[# w .: env_subst vs]) as Heq by autosubst.
      rewrite -/of_val Heq. iModIntro.
      iApply (IHtyped3 _ _ (w :: vs)).
      { iApply interp_un_env_cons. auto. }
      iPureIntro.
      eapply ord_neg_left; [|done]. by apply ord_join_left.
  Qed.

  Lemma un_log_related_alloc Γ pc e τ
        (Hflow : τ ↘ pc)
        (IHtyped : Γ # pc ⊨ᵤ e : τ)
    : Γ # pc ⊨ᵤ Alloc e : TRef τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind AllocCtx v m x "#Hv" IHtyped.
    iApply (mwp_fupd (mwpd_step_fupd SI)).
    iApply mwp_step_fupd_alloc; [done|].
    iNext; iIntros (l) "Hl".
    iMod (inv_alloc (nroot .@ l) _ (∃ v, l ↦ v ∗ ⌊ τ ⌋ₛ _ _ v)%I
            with "[Hl]") as "#HN"; [eauto|].
    rewrite interp_un_ref_def.
    do 2 iModIntro. iExists (nroot .@ l), l. iSplit; [auto|].
    destruct τ. case_bool_decide; iIntros (E) "%".
    - eapply interp_label_flowsto in Hflow.
      by eassert ((⌊ pc ⌋ₗ _) ⊑ ζ); first etransitivity.
    - iInv (nroot .@ l) as "Hl" "Hclose". by iFrame.
  Qed.


  Lemma un_log_related_store Γ pc e1 e2 τ ℓ
        (Hflow : τ ↘ pc ⊔ₛ ℓ)
        (IHtyped1 : Γ # pc ⊨ᵤ e1 : TRef τ @ ℓ)
        (IHtyped2 : Γ # pc ⊨ᵤ e2 : τ)
    : Γ # pc ⊨ᵤ Store e1 e2 : TUnit @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (StoreLCtx _) v k x "#Hv" IHtyped1.
    rewrite interp_un_ref_def.
    smart_mwp_bind (StoreRCtx _) w m y "#Hw" IHtyped2.
    destruct τ as [ℓ' ?]. iDestruct "Hv" as (N l) "[-> Hv]".
    rewrite bool_decide_eq_false_2; last first.
    { eapply interp_label_flowsto in Hflow.
      destruct (join_ord_inv _ _ _ Hflow) as [??].
      by eapply (ord_neg_left (⌊ pc ⌋ₗ _)). }
    iApply (mwp_atomic ((mwpd_step_fupd SI)) _ StronglyAtomic).
    iMod ("Hv" with "[]") as "[Hl Hclose]"; first solve_ndisj.
    iModIntro.
    iDestruct "Hl" as (w') "[Hl ?]".
    iApply (mwp_step_fupd_store with "[//]").
    iFrame. iIntros "!> Hl".
    rewrite interp_un_unit_def.
    iMod ("Hclose" with "[Hl]") as "_"; auto.
  Qed.

  Lemma un_log_related_load Γ pc e τ τ' ℓ
        (Hsub : τ <:ₛ τ')
        (Hflow : τ' ↘ ℓ)
        (IHtyped : Γ # pc ⊨ᵤ e : TRef τ @ ℓ)
    : Γ # pc ⊨ᵤ Load e : τ'.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind LoadCtx v m x "#Hv" IHtyped.
    rewrite interp_un_ref_def.
    destruct τ as [ℓ1 t1]; destruct τ' as [ℓ2 t2].
    iDestruct "Hv" as (N l) "[-> Hv]".
    case_bool_decide.
    - iApply (mwp_atomic ((mwpd_step_fupd SI)) _ StronglyAtomic _ ∅).
      iMod ("Hv" with "[]") as "Hl"; first solve_ndisj.
      iDestruct "Hl" as (w) "[[Hl #Hw] Hclose]".
      iMod (fupd_intro_mask' _ ∅) as "Hclose'"; first set_solver.
      iModIntro.
      iApply (mwp_step_fupd_load with "[//]").
      iFrame. iIntros "!> Hl". iMod "Hclose'" as "_".
      iMod ("Hclose" with "[Hl]") as "_"; first auto.
      by iApply interp_un_secsubtype.
    - iApply (mwp_atomic ((mwpd_step_fupd SI)) _ StronglyAtomic _ ∅).
      iMod ("Hv" with "[]") as "Hl"; first solve_ndisj.
      iDestruct "Hl" as "[Hl Hclose]". iDestruct "Hl" as (w) "[Hl #?]".
      iMod (fupd_intro_mask' _ ∅) as "Hclose'"; first set_solver.
      iModIntro.
      iApply (mwp_step_fupd_load with "[//]").
      iFrame. iNext. iIntros "Hl". iMod "Hclose'" as "_".
      iMod ("Hclose" with "[Hl]") as "_"; first auto.
      by iApply interp_un_secsubtype.
  Qed.

  Lemma un_log_related_subtype Γ pc pc' e τ τ'
        (Hpc : pc ⊑ₛ pc')
        (Hsub : τ' <:ₛ τ)
        (IHtyped : Γ # pc' ⊨ᵤ e : τ')
    : Γ # pc ⊨ᵤ e : τ.
  Proof.
    iIntros (????) "#? %".
    iApply (mwp_wand_r (mwpd_step_fupd SI)).
    iSplitL.
    { iApply IHtyped; [done|]. iPureIntro.
      eapply interp_label_flowsto in Hpc.
      by eapply (ord_neg_left (⌊ pc ⌋ₗ _)). }
    iIntros (v m x) "#Hv".
    by iApply interp_un_secsubtype.
  Qed.

  Lemma un_log_related_tlam Γ pc e τ ℓₑ
        (IHtyped : hsubst_sectype (ren (+1)) <$> Γ # ℓₑ ⊨ᵤ e : τ)
    : Γ # pc ⊨ᵤ TLam e : TForall ℓₑ τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_tforall_def.
    iIntros "!> !>" (???).
    iApply mwp_step_fupd_pure_step; [done|]. iNext.
    iApply IHtyped; [|done].
    by iApply interp_un_env_ren.
  Qed.

  Lemma un_log_related_tapp Γ pc e τ ℓ ℓₑ (t' : type)
        (Hflow : pc ⊔ₛ ℓ ⊑ₛ ℓₑ)
        (IHtyped : Γ # pc ⊨ᵤ e : TForall ℓₑ τ @ ℓ)
    : Γ # pc ⊨ᵤ TApp e : τ.|[t'/].
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind TAppCtx v m x "#Hv" IHtyped.
    rewrite interp_un_tforall_def.
    iApply (mwp_wand_r (mwpd_step_fupd SI)); iSplitL.
    { iApply ("Hv" $! (⌊ t' ⌋ Δ ρ)); iPureIntro; [apply _|].
      eapply interp_label_flowsto in Hflow.
      destruct (join_ord_inv _ _ _ Hflow) as [??].
      by eapply (ord_neg_left (⌊ pc ⌋ₗ _)). }
    iIntros (w k y) "Hw".
    by iApply (interp_un_sec_type_subst_up _ [] _ 0).
  Qed.

  Lemma un_log_related_tllam Γ pc e τ ℓₑ
        (IHtyped : hsubst_label_sectype (ren (+1)) <$> Γ # ℓₑ ⊨ᵤ e : τ)
    : Γ # pc ⊨ᵤ TLLam e : TLForall ℓₑ τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#Henv %".
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_tlforall_def.
    iIntros "!> !>" (ℓ ?).
    iApply mwp_step_fupd_pure_step; [done|]. iNext.
    iApply mwp_wand_r; iSplitL.
    iApply (IHtyped _ (ℓ :: ρ)); auto.
    { by iApply interp_un_env_label_ren. }
    iIntros (???). auto.
  Qed.

  Lemma un_log_related_tlapp Γ pc e τ (ℓ ℓₑ ℓ' : label_term)
        (Hflow  : pc ⊔ₛ ℓ ⊑ₛ ℓₑ.[ℓ'/])
        (IHtyped : Γ # pc ⊨ᵤ e : TLForall ℓₑ τ @ ℓ)
    : Γ # pc ⊨ᵤ TLApp e : τ.|[ℓ'/].
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind TLAppCtx v m x "#Hv" IHtyped.
    rewrite interp_un_tlforall_def.
    iApply (mwp_wand_r (mwpd_step_fupd SI)); iSplitL.
    { iApply ("Hv" $! (⌊ ℓ' ⌋ₗ ρ)); iPureIntro.
      pose proof (interp_label_flowsto _ _ Hflow ρ) as Hflow'.
      simpl in Hflow'.
      destruct (join_ord_inv _ _ _ Hflow') as [??].
      eapply (ord_neg_left (⌊ pc ⌋ₗ ρ)); [|done].
      by rewrite -(interp_label_subst_up _ _ []). }
    iIntros (???) "Hw".
    by iApply (interp_un_sec_label_subst_up _ []).
  Qed.

  Lemma un_log_related_pack Γ pc e τ t
        (IHtyped : Γ # pc ⊨ᵤ e : τ.|[t/])
    : Γ # pc ⊨ᵤ Pack e : TExist τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind PackCtx w n x "#Hv" IHtyped.
    iApply (mwp_value (mwpd_step_fupd _)); umods.
    rewrite interp_un_exist_def.
    do 2 iModIntro. iExists (⌊ t ⌋ _ _)%I.
    iSplit; [iPureIntro; apply _|].
    iExists _. iSplit; [done|].
    by iApply (interp_un_sec_type_subst_up _ [] _ 0).
  Qed.

  Lemma un_log_related_unpack Γ pc e1 e2 τ1 τ2 ℓ
      (IHtyped1 : Γ # pc⊨ᵤ e1 : TExist τ1 @ ℓ)
      (IHtyped2 : τ1 :: (hsubst_sectype (ren (+1)) <$> Γ) # pc ⊔ₛ ℓ ⊨ᵤ e2 : (hsubst_sectype (ren (+1)) τ2))
    : Γ # pc ⊨ᵤ Unpack e1 e2 : τ2.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind (UnpackCtx _) w n x "#Hv" IHtyped1.
    rewrite interp_un_exist_def.
    iDestruct "Hv" as (τi) "[% #Hv]".
    iDestruct "Hv" as (v) "[-> Hv]".
    iApply mwp_step_fupd_pure_step; [done|].
    iModIntro. rewrite -/of_val.
    assert (e2.[up (env_subst vs)].[# v/] =
            e2.[# v .: env_subst vs]) as Heq by autosubst.
    rewrite -/of_val Heq.
    iApply mwp_wand_r; iSplitL.
    { iApply (IHtyped2 (τi :: Δ) _ (_ :: _)).
      - iApply interp_un_env_cons. iFrame "#".
        by iApply interp_un_env_ren.
      - iPureIntro. eapply ord_neg_left; [|done]. by apply ord_join_left. }
    iIntros (w ??) "Hw".
    by iApply (interp_un_sec_type_weaken _ [] [_] _ 0).
  Qed.

  Lemma un_log_related_fold Γ pc v τ
        (IHtyped : Γ # pc ⊨ᵤ v : τ.|[TRec τ/])
    : Γ # pc ⊨ᵤ Fold v : TRec τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind FoldCtx w n x "#Hv" IHtyped.
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    rewrite interp_un_rec_def.
    rewrite fixpoint_interp_un_rec1_eq /interp_un_rec1.
    do 2 iModIntro. iExists _; iSplit; [done|]. iModIntro.
    change (fixpoint _) with (⌊ TRec τ ⌋ Δ ρ).
    by iApply (interp_un_sec_type_subst_up _ [] _ 0).
  Qed.

  Lemma un_log_related_unfold Γ pc e τ ℓ
        (IHtyped : Γ # pc ⊨ᵤ e : TRec τ @ ℓ)
    : Γ # pc ⊨ᵤ Unfold e : τ.|[TRec τ/].
  Proof.
    iIntros (????) "#? %".
    smart_mwp_bind UnfoldCtx w n x "#Hw" IHtyped.
    rewrite interp_un_rec_def fixpoint_interp_un_rec1_eq /interp_un_rec1 /=.
    change (fixpoint _) with (⌊ TRec τ ⌋ Δ ρ).
    iDestruct "Hw" as (v) "[-> #Hv]".
    iApply mwp_step_fupd_pure_step; [done|].
    rewrite -/of_val. iModIntro.
    iApply mwp_value; umods.
    by iApply (interp_un_sec_type_subst_up _ [] _ 0).
  Qed.

  Theorem fundamental_un Γ pc e τ :
    Γ # pc ⊢ₜ e : τ → Γ # pc ⊨ᵤ e : τ.
  Proof.
    induction 1; iIntros (????) "#Hctx %".
    - by iApply un_log_related_unit.
    - by iApply un_log_related_bool.
    - by iApply un_log_related_nat.
    - by iApply un_log_related_var.
    - by iApply un_log_related_lam.
    - by iApply un_log_related_binop.
    - by iApply un_log_related_app.
    - by iApply un_log_related_letin.
    - by iApply un_log_related_seq.
    - by iApply un_log_related_tlam.
    - by iApply un_log_related_tapp.
    - by iApply un_log_related_tllam.
    - by iApply un_log_related_tlapp.
    - by iApply un_log_related_if.
    - by iApply un_log_related_pair.
    - by iApply un_log_related_proj1.
    - by iApply un_log_related_proj2.
    - by iApply un_log_related_inl.
    - by iApply un_log_related_inr.
    - by iApply un_log_related_case.
    - by iApply un_log_related_alloc.
    - by iApply un_log_related_store.
    - by iApply un_log_related_load.
    - by iApply un_log_related_pack.
    - by iApply un_log_related_unpack.
    - by iApply un_log_related_fold.
    - by iApply un_log_related_unfold.
    - by iApply un_log_related_subtype.
  Qed.

End fundamental.
