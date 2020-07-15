From iris.algebra Require Import list.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lang typing fundamental_unary
     logrel_binary rules_binary.

Section bin_log_def.
  Context `{!secG Σ}.
  Context `{SecurityLattice label}.

  Definition bi_log_related (Γ : list sectype) (e1 e2 : expr) (τ : sectype) :=
    ∀ Θ ρ vvs,
      envs_Persistent Θ →
      env_coherent Θ ∗
      ⟦ Γ ⟧* Θ ρ vvs ⊢ ⟦ τ ⟧ₑ Θ ρ (e1.[env_subst (vvs.*1)], e2.[env_subst (vvs.*2)]).

End bin_log_def.

Notation "Γ ⊨ e '≤ₗ' e' : τ" :=
  (bi_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{secG Σ}.
  Context `{SecurityLattice label}.

  Notation D := (val -d> iPropO Σ).
  Notation P := (val * val -d> iPropO Σ).
  Notation T := (prodO P (prodO D D)).

  Implicit Types Θ : listO T.

  Notation proj_bin Θ := (Θ.*1 : listO P).
  Notation projl Θ := (Θ.*2.*1 : listO D).
  Notation projr Θ := (Θ.*2.*2 : listO D).

  Local Tactic Notation "smart_ic_bind" uconstr(ctx) ident(v) ident(n)
        ident(x) constr(Hv) constr(Hp) :=
    iApply (ic_left_strong_bind SI_left SI_right (fill [ctx]) (fill [ctx]));
    iApply (ic_wand_r with "[-]"); iSplitL; [iApply Hp; iFrame "#"|];
    iIntros (v n x) Hv; cbn.

  Lemma up_env_subst e vs v :
    e.[up (env_subst vs)].[# v/] = e.[# v .: env_subst vs].
  Proof. autosubst. Qed.

  Hint Rewrite up_env_subst : autosubst.

  Lemma interp_secsubtype τ1 τ2 Θ ρ vv :
    τ1 <:ₛ τ2 →
    envs_Persistent Θ →
    env_coherent Θ -∗ ⟦ τ1 ⟧ₛ Θ ρ vv -∗ ⟦ τ2 ⟧ₛ Θ ρ vv.
  Proof.
    intros Hsub. move: Θ ρ vv.
    elim Hsub using secsubtype_mut
      with (P := (λ t1 t2 H, ∀ Θ ρ vv,
        t1 <: t2 → envs_Persistent Θ →
        env_coherent Θ -∗ ⟦ t1 ⟧ Θ ρ vv -∗ ⟦ t2 ⟧ Θ ρ vv)); [auto|..].
    - iIntros (t1 t2 t3 ? Ht1 ? Ht2 ?????) "#? #?".
      iApply Ht2; try done. by iApply Ht1.
    - iIntros (τ1'' τ1' τ2' τ2'' ??? Hτ1 ? Hτ2 Hflow ????).
      move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      rewrite !interp_arrow_def !interp_un_arrow_def.
      iIntros (?) "#? #[H1 [H2 H3]]". repeat iSplit; iModIntro.
      + iIntros (?) "#?". iApply ic_wand_r; iSplitL.
        * iApply "H1". by iApply Hτ1.
        * iIntros (???) "?". cbn. by iApply Hτ2.
      + iIntros (?) "#Hτ1 %".
        iApply ic_wand_r. iSplitL.
        * iApply "H2"; [by iApply (interp_un_secsubtype with "Hτ1")|].
          iPureIntro. apply: ord_neg_left=>//.
        * iIntros (???) "#Hτ2". by iApply (interp_un_secsubtype with "Hτ2").
      + iIntros (v) "#Hτ1 %".
        iApply ic_wand_r; iSplitL.
        * iApply "H3"; [by iApply (interp_un_secsubtype with "Hτ1")|].
          iPureIntro. apply: ord_neg_left=>//.
        * iIntros (???) "#Hτ2". by iApply (interp_un_secsubtype with "Hτ2").
    - iIntros (???? Hflow ? H ?????).
      move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      rewrite !interp_tforall_def !interp_un_tforall_def.
      iIntros "#Hcoh #[H1 [H2 H3]]". repeat iSplit; iModIntro.
      + iIntros (τR τi1 τi2 HPb Hτi1 Hτi2) "#Hsum". iApply ic_wand_r; iSplitL.
        * by iApply ("H1" $! _ _ _ HPb Hτi1 Hτi2).
        * iIntros (???) "? /=". iApply H; [|done].
          iApply big_sepL_cons; auto.
      + iIntros (???).
        iApply ic_wand_r; iSplitL.
        * iApply "H2"; auto. iPureIntro. apply: ord_neg_left=>//.
        * iIntros (???) "Hτ0". by iApply (interp_un_secsubtype with "Hτ0").
      + iIntros (???). iApply ic_wand_r; iSplitL.
        * iApply "H3"; eauto. iPureIntro.
          apply: ord_neg_left=>//.
        * iIntros (???) "Hτ0". by iApply (interp_un_secsubtype with "Hτ0").
    - iIntros (???? Hflow ? H ?????).
      move: Hflow => /interp_label_flowsto Hflow.
      rewrite !interp_tlforall_def !interp_un_tlforall_def.
      iIntros "#? #[H1 [H2 H3]]". repeat iSplit; iModIntro.
      + iIntros (?). iApply ic_wand_r; iSplitL.
        * by iApply "H1".
        * iIntros (???) "? /=". by iApply H.
      + iIntros (??). iApply ic_wand_r; iSplitL.
        * iApply "H2". iPureIntro. apply: ord_neg_left; by [apply Hflow|].
        * iIntros (???) "Hτ0 /=". by iApply (interp_un_secsubtype with "Hτ0").
      + iIntros (??). iApply ic_wand_r; iSplitL.
        * iApply "H3". iPureIntro. apply: ord_neg_left; by [apply Hflow|].
        * iIntros (???) "Hτ0". by iApply (interp_un_secsubtype with "Hτ0").
    - iIntros (????? Hτ1 ? Hτ2 ?????) "#Hcoh".
      rewrite !interp_prod_def. iDestruct 1 as (????) "[-> [-> [#H1 #H2]]]".
      iPoseProof (Hτ1 with "Hcoh H1") as "H1'".
      iPoseProof (Hτ2 with "Hcoh H2") as "H2'".
      iExists _, _, _, _; eauto.
    - iIntros (τ1' τ1'' τ2' τ2'' ? Hτ1 ? Hτ2 ?????) "#Hcoh".
      rewrite !interp_sum_def. iDestruct 1 as (??) "[ [-> H] | [-> H]]".
      + iExists _, _; iPoseProof (Hτ1 with "Hcoh H") as "H'". auto.
      + iExists _, _; iPoseProof (Hτ2 with "Hcoh H") as "H'". auto.
    - iIntros (??? IH ?????) "#Hcoh".
      rewrite !interp_rec_def !fixpoint_interp_rec1_eq /interp_rec1 /=.
      iDestruct 1 as (?) "[-> #Hτ0]".
      iModIntro. iExists _. iSplit; [done|]. iModIntro.
      replace (fixpoint _) with (⟦ TRec τ0 ⟧ Θ ρ); [|done].
      replace (fixpoint _) with (⟦ TRec τ3 ⟧ Θ ρ); [|done].
      iApply (interp_sec_type_subst_up _ []).
      iDestruct ((interp_sec_type_subst_up _ []) with "Hτ0") as "H".
      asimpl. by iApply IH.
    - iIntros (ℓ ℓ' t1 t2 Hflow ? IH ????) "#Hcoh". rewrite !interp_sec_def.
      do 2 case_bool_decide.
      + by iApply IH.
      + iIntros "#Ht1". iDestruct (IH with "Hcoh Ht1") as "Ht2"; [done|].
        iApply (bi_subsume_un with "[$Hcoh $Ht2]").
      + exfalso. move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
        apply: (ord_neg_left _ _ _ Hflow)=> //.
      + iIntros "[H1 H2]".
        iSplit; iApply interp_un_secsubtype; by [constructor|].
  Qed.

  Lemma bi_log_related_unit Γ : Γ ⊨ Unit ≤ₗ Unit : TUnit @ ⊥ₛ.
  Proof.
    iIntros (????) "[#Hcoh #HΓ]".
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_unit_def.
    rewrite bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_bool Γ b : Γ ⊨ Bool b ≤ₗ Bool b : TBool @ ⊥ₛ.
  Proof.
    iIntros (????) "[#Hcoh #HΓ]".
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_bool_def.
    rewrite bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_nat Γ n : Γ ⊨ Nat n ≤ₗ Nat n : TNat @ ⊥ₛ.
  Proof.
    iIntros (????) "[#Hcoh #HΓ]".
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_nat_def.
    rewrite bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_var Γ x τ :
    Γ !! x = Some τ → Γ ⊨ Var x ≤ₗ Var x : τ.
  Proof.
    iIntros (Hx Θ ρ vvs ?) "[#Hcoh #HΓ] /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[%Heq Hv]"; [done|].
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq /=; auto.
    iApply (ic_value ic_binary); umods.
    by iApply (ic_value (icd_right SI_right)); umods.
  Qed.

  Lemma bi_log_related_lam Γ ℓₑ e e' τ1 τ2
        (Htyped1 : τ1 :: Γ # ℓₑ ⊢ₜ e : τ2)
        (Htyped2 : τ1 :: Γ # ℓₑ ⊢ₜ e' : τ2)
        (IHtyped : τ1 :: Γ ⊨ e ≤ₗ e' : τ2)
    : Γ ⊨ Lam e ≤ₗ Lam e' : TArrow ℓₑ τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]". rewrite /interp_expr.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2; [|by apply ord_bottom].
    iModIntro. rewrite !interp_un_arrow_def.
    repeat iSplit; iModIntro.
    - iIntros ([w1 w2]) "#Hww".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply ic_left_pure_step; [done|]. iNext.
      iApply ic_left_pure_step_index; [done|].
      rewrite !up_env_subst.
      iApply (ic_wand_r ic_binary); iSplitL.
      { iApply (IHtyped _ _ ((w1, w2) :: _)). iFrame "#".
        iApply (interp_env_cons with "[$]"). }
      by iIntros (?? []) "? /=".
    - iIntros (v) "Hv %".
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[HΓ1 _]".
      iDestruct (interp_un_env_cons with "[$Hv $HΓ1]") as "#HΓ'".
      rewrite up_env_subst.
      by iApply (fundamental_un with "HΓ'").
    - iIntros (v) "Hv %".
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[_ HΓ2]".
      iDestruct (interp_un_env_cons with "[$Hv $HΓ2]") as "#HΓ'".
      rewrite up_env_subst.
      by iApply (fundamental_un with "HΓ'").
  Qed.

  Lemma bi_log_related_binop Γ op e1 e1' e2 e2' ℓ1 ℓ2
        (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : TNat @ ℓ1)
        (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : TNat @ ℓ2)
    : Γ ⊨ BinOp op e1 e2 ≤ₗ BinOp op e1' e2' : (binop_type op) @ (ℓ1 ⊔ₛ ℓ2).
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (BinOpLCtx _ _) v n x "#Hv" IHtyped1.
    smart_ic_bind (BinOpRCtx _ _) w m y "#Hw" IHtyped2.
    destruct (decide (⌊ ℓ1 ⌋ₗ ρ ⊔ ⌊ ℓ2 ⌋ₗ ρ ⊑ ζ)) as [Hflow|Hnflow].
    - destruct (join_ord_inv _ _ _ Hflow) as [? ?].
      rewrite !interp_sec_def !interp_nat_def ?bool_decide_eq_true_2 //=.
      iDestruct "Hv" as (? b1 -> ->) "->".
      iDestruct "Hw" as (? b2 -> ->) "->".
      iApply ic_left_pure_step; [done|]. iNext.
      iApply ic_left_pure_step_index; [done|].
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right SI_right)); umods.
      rewrite interp_sec_def bool_decide_eq_true_2 //.
      destruct op; simpl; rewrite ?interp_bool_def ?interp_nat_def;
        try case_bool_decide; eauto.
    - iDestruct (secbin_subsumes_secun with "[$Hcoh $Hv]") as "[#Hv1 #Hv2]".
      iDestruct (secbin_subsumes_secun with "[$Hcoh $Hw]") as "[#Hw1 #Hw2] /=".
      rewrite !interp_un_sec_def !interp_un_nat_def.
      iDestruct "Hv1" as (b1) "->". iDestruct "Hv2" as (b1') "->".
      iDestruct "Hw1" as (b2) "->". iDestruct "Hw2" as (b2') "->".
      iApply ic_left_pure_step; [done|]. iNext.
      iApply ic_left_pure_step_index; [done|].
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right SI_right)); umods.
      iEval (rewrite interp_sec_def).
      rewrite bool_decide_eq_false_2 // !interp_un_sec_def.
      destruct op; simpl; rewrite ?interp_un_bool_def ?interp_un_nat_def;
        try case_bool_decide; eauto.
  Qed.

  Lemma bi_log_related_app Γ pc ℓₑ e1 e1' e2 e2' ℓ τ1 τ2
      (Hflow1 : τ2 ↘ ℓ)
      (Hflow2 : pc ⊔ₛ ℓ ⊑ₛ ℓₑ)
      (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : TArrow ℓₑ τ1 τ2 @ ℓ)
      (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : τ1)
  : Γ ⊨ App e1 e2 ≤ₗ App e1' e2' : τ2.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (AppLCtx _) v n x "#Hv" IHtyped1.
    smart_ic_bind (AppRCtx _) w m y "#Hw" IHtyped2.
    destruct τ2 as [ℓ' t2]. rewrite interp_sec_def interp_arrow_def.
    case_bool_decide as Hflow.
    - iDestruct "Hv" as "[#Hv _]". by iApply ("Hv" with "Hw").
    - iDestruct "Hv" as "[#Hv1 #Hv2] /=".
      move: Hflow1 => /interp_label_flowsto /(_ ρ) Hflow1.
      move: Hflow2=> /interp_label_join_ord_inv /(_ ρ) [Hflow2 Hflow3].
      iDestruct (secbin_subsumes_secun with "[$Hcoh $Hw]") as "#[Hw1 Hw2] /=".
      rewrite !interp_un_sec_def !interp_un_arrow_def.
      iApply ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iApply ("Hv1" with "Hw1").
        iPureIntro. by eapply ord_neg_left. }
      iIntros (???) "#? /=".
      iApply (ic_wand_r (icd_step_fupd SI_right)).
      iSplitL.
      { iApply ("Hv2" with "Hw2").
        iPureIntro. by eapply ord_neg_left. }
      iIntros (???) "#?". rewrite !interp_sec_def.
      move: (ord_neg_left _ _ _ Hflow1 Hflow)=>?.
      rewrite bool_decide_eq_false_2 //. iFrame "#".
  Qed.

  Lemma bi_log_related_letin Γ e1 e1' e2 e2' τ1 τ2
        (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : τ1)
        (IHtyped2 : τ1 :: Γ ⊨ e2 ≤ₗ e2' : τ2)
    : Γ ⊨ LetIn e1 e2 ≤ₗ LetIn e1' e2' : τ2.
  Proof.
    iIntros (????) "[#? #HΓ]".
    smart_ic_bind (LetInCtx _) v k x "#Hv" IHtyped1.
    iApply ic_left_pure_step; [done|]. iNext.
    iApply ic_left_pure_step_index; [done|]. cbn.
    rewrite !up_env_subst.
    iApply (IHtyped2 _ _ ((_,_) :: vvs)).
    iFrame "#".
    iApply interp_env_cons. auto.
  Qed.

  Lemma bi_log_related_seq Γ e1 e1' e2 e2' τ1 τ2
        (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : τ1)
        (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : τ2)
    : Γ ⊨ Seq e1 e2 ≤ₗ Seq e1' e2' : τ2.
  Proof.
    iIntros (????) "[#? #HΓ]".
    smart_ic_bind (SeqCtx _) v k x "#Hv" IHtyped1.
    iApply ic_left_pure_step; [done|]. iNext.
    iApply ic_left_pure_step_index; [done|]. cbn.
    iApply IHtyped2; auto.
  Qed.

  Lemma bi_log_related_tlam Γ e e' τ (ℓₑ : label_term)
        (Htyped1 : hsubst_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e : τ )
        (Htyped2 : hsubst_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e' : τ)
        (IHtyped : hsubst_sectype (ren (+1)) <$> Γ ⊨ e ≤ₗ e' : τ)
    : Γ ⊨ TLam e ≤ₗ TLam e' : TForall ℓₑ τ @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_tforall_def !interp_un_tforall_def.
    rewrite bool_decide_eq_true_2; [|by apply ord_bottom].
    iModIntro. repeat iSplit; iModIntro.
    - iIntros (tR τi1 τi2 ???) "#Hsub".
      iApply ic_left_pure_step; [done|]. iNext.
      iApply ic_left_pure_step_index; [done|]. cbn.
      iApply IHtyped. iSplit; last by iApply interp_bi_env_ren.
      iApply big_sepL_cons; iFrame "#".
    - iIntros (???).
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[HΓ1 _]".
      iDestruct (interp_un_env_ren with "HΓ1") as "HΓ1'".
      by iApply (fundamental_un with "HΓ1'").
    - iIntros (???).
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[_ HΓ2]".
      iDestruct (interp_un_env_ren with "HΓ2") as "HΓ2'".
      by iApply (fundamental_un with "HΓ2'").
  Qed.

  Lemma bi_log_related_tapp Γ pc e e' τ t' ℓ ℓₑ
        (Hflow1 : τ.|[t'/] ↘ ℓ)
        (Hflow2 : pc ⊔ₛ ℓ ⊑ₛ ℓₑ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : TForall ℓₑ τ @ ℓ)
    : Γ ⊨ TApp e ≤ₗ TApp e' : τ.|[t'/].
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (TAppCtx) v n x "#Hv" IHtyped.
    rewrite interp_sec_def interp_tforall_def.
    case_bool_decide as Hflow.
    - iDestruct "Hv" as "#(Hbin & _ & _)".
      iApply (ic_wand_r ic_binary); iSplitL.
      { iApply ("Hbin" $! (⟦ t' ⟧ Θ ρ)
                       (⌊ t' ₗ⌋ (projl Θ) ρ) (⌊ t' ᵣ⌋ (projr Θ) ρ));
          try (iPureIntro; apply _).
        iModIntro. iIntros (?) "Ht'".
        iApply (bi_subsume_un with "[$Hcoh $Ht']"). }
      iIntros (???) "Hτ /=".
      by iApply (interp_sec_type_subst_up _ []).
    - rewrite !interp_un_sec_def !interp_un_tforall_def.
      iDestruct "Hv" as "[#Hv1 #Hv2] /=".  destruct τ as [ℓ' t ].
      move: Hflow1 => /interp_label_flowsto /(_ ρ) Hflow1.
      move: Hflow2=> /interp_label_join_ord_inv /(_ ρ) [Hflow2 Hflow3].
      move: (ord_neg_left _ _ _ Hflow1 Hflow)=>?.
      move: (ord_neg_left _ _ _ Hflow3 Hflow)=>?.
      iApply ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iApply ("Hv1" $! (⌊ t' ₗ⌋ (projl Θ) ρ)); [|done].
        iPureIntro; apply _. }
      iIntros (???) "#Ht1".
      iApply ic_wand_r; iSplitL.
      { iApply ("Hv2" $! (⌊ t' ᵣ⌋ (projr Θ) ρ)); [|done].
        iPureIntro; apply _. }
      iIntros (???) "#Ht2". asimpl. rewrite interp_sec_def.
      rewrite bool_decide_eq_false_2 //.
      iSplit; by iApply (interp_un_sec_type_subst_up (t @ ℓ') [] _ 0).
  Qed.

  Lemma bi_log_related_tllam Γ e e' τ ℓₑ
        (Htyped1 : hsubst_label_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e : τ )
        (Htyped2 : hsubst_label_sectype (ren (+1)) <$> Γ # ℓₑ ⊢ₜ e' : τ )
        (IHtyped : hsubst_label_sectype (ren (+1)) <$> Γ ⊨ e ≤ₗ e' : τ)
    : Γ ⊨ TLLam e ≤ₗ TLLam e' : TLForall ℓₑ τ @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    rewrite interp_sec_def interp_tlforall_def
            !interp_un_sec_def !interp_un_tlforall_def.
    rewrite bool_decide_eq_true_2; [|by apply ord_bottom].
    iModIntro. repeat iSplit; iModIntro.
    - iIntros (?).
      iApply ic_left_pure_step; [done|]. iNext.
      iApply ic_left_pure_step_index; [done|]. cbn.
      iApply IHtyped. iFrame "#". by iApply interp_bi_env_label_ren.
    - iIntros (??).
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[HΓ1 _]".
      iDestruct (interp_un_env_label_ren with "HΓ1") as "HΓ1'".
      by iApply (fundamental_un with "HΓ1'").
    - iIntros (ℓ ?).
      iApply ic_step_fupd_pure_step; [done|]. iNext.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[_ HΓ2]".
      iDestruct (interp_un_env_label_ren with "HΓ2") as "HΓ2'".
      by iApply (fundamental_un with "HΓ2'").
  Qed.

  Lemma bi_log_related_tlapp Γ pc e e' τ (ℓ ℓ' ℓₑ : label_term)
        (Hflow1 : τ.|[ℓ'/] ↘ ℓ)
        (Hflow2 : pc ⊔ₛ ℓ ⊑ₛ ℓₑ.[ℓ'/])
        (IHtyped : Γ ⊨ e ≤ₗ e' : TLForall ℓₑ τ @ ℓ)
    : Γ ⊨ TLApp e ≤ₗ TLApp e' : τ.|[ℓ'/].
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (TLAppCtx) v n x "#Hv" IHtyped.
    rewrite interp_sec_def interp_tlforall_def.
    case_bool_decide as Hflow.
    - iDestruct "Hv" as "#(Hbin & _)".
      iApply (ic_wand_r ic_binary); iSplitL.
      { iApply ("Hbin" $! (⌊ ℓ' ⌋ₗ ρ)). }
      iIntros (???) "#Hτ /=".
      by iApply (interp_sec_bi_label_subst_up _ _ _ []).
    - rewrite !interp_un_sec_def !interp_un_tlforall_def.
      iDestruct "Hv" as "[#Hv1 #Hv2]".
      destruct τ as [ℓ'' t ].
      move: Hflow1 => /interp_label_flowsto /(_ ρ) Hflow1.
      move: Hflow2=> /interp_label_join_ord_inv /(_ ρ) [Hflow2 Hflow3].
      move: (ord_neg_left _ _ _ Hflow1 Hflow)=>Hflow4.
      move: (ord_neg_left _ _ _ Hflow3 Hflow)=>Hflow5.
      move: (ord_neg_left _ _ _ Hflow1 Hflow)=>Hflow6.
      iApply ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iApply ("Hv1" $! (⌊ ℓ' ⌋ₗ ρ)). iPureIntro.
        rewrite -interp_label_subst1 //. }
      iIntros (???) "#Ht1".
      iApply ic_wand_r; iSplitL.
      { iApply ("Hv2" $! (⌊ ℓ' ⌋ₗ ρ)). iPureIntro.
        rewrite -interp_label_subst1 //. }
      iIntros (???) "#Ht2 /=". asimpl.
      rewrite interp_sec_def !interp_un_sec_def bool_decide_eq_false_2 //.
      iSplit; by iApply interp_un_label_subst1.
  Qed.

  Lemma bi_log_related_if Γ pc e e' e1 e1' e2 e2' ℓ τ
      (Hflow : τ ↘ ℓ)
      (Htyped1 : Γ # pc ⊔ₛ ℓ ⊢ₜ e1 : τ)
      (Htyped2 : Γ # pc ⊔ₛ ℓ ⊢ₜ e1' : τ)
      (Htyped3 : Γ # pc ⊔ₛ ℓ ⊢ₜ e2 : τ)
      (Htyped4 : Γ # pc ⊔ₛ ℓ ⊢ₜ e2' : τ)
      (IHtyped : Γ ⊨ e ≤ₗ e' : TBool @ ℓ)
      (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : τ)
      (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : τ)
    : Γ ⊨ If e e1 e2 ≤ₗ If e' e1' e2' : τ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ] /=".
    smart_ic_bind (IfCtx _ _) v n x "#Hv" IHtyped.
    rewrite interp_sec_def interp_bool_def /=.
    case_bool_decide as Hflow'.
    - iDestruct "Hv" as (b1 []) "(-> & -> & ->)".
      + iApply ic_left_pure_step; [done|]. iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_wand_r; iSplitL; [iApply IHtyped1; iFrame "#"|].
        iIntros (w m []) "Ht /=".
        by iApply (interp_secsubtype with "Hcoh Ht").
      + iApply ic_left_pure_step; [done|]. iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_wand_r; iSplitL; [iApply IHtyped2; iFrame "#"|].
        iIntros (w m []) "Ht /=".
        by iApply (interp_secsubtype with "Hcoh Ht").
    - rewrite !interp_un_sec_def !interp_un_bool_def.
      iDestruct "Hv" as "[Hv Hx1]".
      iDestruct "Hv" as (b1) "->". iDestruct "Hx1" as (b2) "->".
      destruct b1, b2.
      + iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_wand_r; iSplitL; [iApply IHtyped1; iFrame "#"|].
        iIntros (w m []) "Ht /=".
        by iApply (interp_secsubtype with "Hcoh Ht").
      + iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_un_bi_lr. cbn.
        iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[#HΓr #HΓl]".
        iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
        { iApply (fundamental_un with "HΓr"); [done|].
          iPureIntro. by apply ord_join_neg_right. }
        iIntros (v m y) "Hv".
        iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
        { iApply (fundamental_un with "HΓl"); [done|].
          iPureIntro. by apply ord_join_neg_right. }
        iIntros (w k z) "Hw". destruct τ.
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
        move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
        apply: ord_neg_left=>//.
      + iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_un_bi_lr; cbn.
        iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[#HΓr #HΓl]".
        iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
        { iApply (fundamental_un with "HΓr"); [done|].
          iPureIntro. by apply ord_join_neg_right. }
        iIntros (v m y) "Hv".
        iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
        { iApply (fundamental_un with "HΓl"); [done|].
          iPureIntro. by apply ord_join_neg_right. }
        iIntros (w k z) "Hw". destruct τ.
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
        move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
        apply: ord_neg_left=>//.
      + iApply ic_left_pure_step; [done|]. iNext.
        iApply ic_left_pure_step_index; [done|].
        iApply ic_wand_r; iSplitL; [iApply IHtyped2; iFrame "#"|].
        iIntros (w m []) "Ht /=".
        by iApply (interp_secsubtype with "Hcoh Ht").
  Qed.

  Lemma bi_log_related_prod Γ e1 e1' e2 e2' τ1 τ2
        (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : τ1)
        (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : τ2)
        : Γ ⊨ Pair e1 e2 ≤ₗ Pair e1' e2' : TProd τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (PairLCtx _) v1 n x "#Hv1" IHtyped1.
    smart_ic_bind (PairRCtx _) v2 m y "#Hv2" IHtyped2.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    iModIntro. iEval (rewrite interp_sec_def).
    rewrite !interp_prod_def bool_decide_eq_true_2; [|by apply ord_bottom].
    iExists _, _, _, _. auto.
  Qed.

  Lemma bi_log_related_proj1 Γ e e' τ1 τ2 ℓ
        (Hflow : τ1 ↘ ℓ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : TProd τ1 τ2 @ ℓ)
    : Γ ⊨ Proj1 e ≤ₗ Proj1 e' : τ1.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ] /=".
    smart_ic_bind Proj1Ctx v1 m y "#Hw" IHtyped.
    destruct τ1 as [ℓ1 t1].
    rewrite interp_sec_def interp_prod_def /=.
    destruct (bool_decide (⌊ ℓ1 ⌋ₗ ρ ⊑ ζ)) eqn:Hflow2.
    - move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      move: Hflow2 => /bool_decide_eq_true_1 ?.
      rewrite !bool_decide_eq_true_2 //; last by etransitivity.
      iDestruct "Hw" as (????) "(-> & -> & Ht1 & Hτ2)".
      iApply ic_left_pure_step; [done|]; iNext.
      iApply ic_left_pure_step_index; [done|].
      rewrite -/of_val /=.
      iApply (ic_value ic_binary); umods.
      by iApply (ic_value (icd_right SI_right)); umods.
    - move: Hflow2 => /bool_decide_eq_false_1 ?.
      destruct (bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)).
      + iDestruct "Hw" as (????) "(-> & -> & Ht1 & Hτ2)".
        iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /=.
        iApply (ic_value ic_binary); umods.
        iApply (ic_value (icd_right SI_right)); umods; iModIntro.
        iFrame "#".
      + iDestruct "Hw" as "[Hv1 Hv2]".
        rewrite !interp_un_sec_def !interp_un_prod_def.
        iDestruct "Hv1" as (??) "(-> & Ht1 & ?)".
        iDestruct "Hv2" as (??) "(-> & Ht1' & ?)".
        iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /=.
        iApply (ic_value ic_binary); umods.
        iApply (ic_value (icd_right SI_right)); umods.
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
  Qed.

  Lemma bi_log_related_proj2 Γ e e' τ1 τ2 ℓ
        (Hflow : τ2 ↘ ℓ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : TProd τ1 τ2 @ ℓ)
    : Γ ⊨ Proj2 e ≤ₗ Proj2 e' : τ2.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind Proj2Ctx v1 m y "#Hw" IHtyped.
    destruct τ2 as [ℓ2 t2].
    rewrite interp_sec_def interp_prod_def /=.
    destruct (bool_decide (⌊ ℓ2 ⌋ₗ ρ ⊑ ζ)) eqn:Hflow2.
    - move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      move: Hflow2 => /bool_decide_eq_true_1 ?.
      rewrite !bool_decide_eq_true_2 //; last by etransitivity.
      iDestruct "Hw" as (????) "(-> & -> & Ht1 & Hτ2)".
      iApply ic_left_pure_step; [done|]; iNext.
      iApply ic_left_pure_step_index; [done|].
      rewrite -/of_val /=.
      iApply (ic_value ic_binary); umods.
      by iApply (ic_value (icd_right SI_right)); umods.
    - move: Hflow2 => /bool_decide_eq_false_1 ?.
      destruct (bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)).
      + iDestruct "Hw" as (????) "(-> & -> & Ht1 & Hτ2)".
        iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /=.
        iApply (ic_value ic_binary); umods.
        iApply (ic_value (icd_right SI_right)); umods; iModIntro.
        iFrame "#".
      + iDestruct "Hw" as "[Hv1 Hv2]".
        rewrite !interp_un_sec_def !interp_un_prod_def.
        iDestruct "Hv1" as (??) "(-> & Ht1 & ?)".
        iDestruct "Hv2" as (??) "(-> & Ht1' & ?)".
        iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /=.
        iApply (ic_value ic_binary); umods.
        iApply (ic_value (icd_right SI_right)); umods.
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
  Qed.

  Lemma bi_log_related_case Γ pc e e' e1 e1' e2 e2' τ τ1 τ2 ℓ
        (Hflow : τ ↘ ℓ)
        (Htyped1  : τ1 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e1  : τ)
        (Htyped1' : τ1 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e1' : τ)
        (Htyped2  : τ2 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e2  : τ)
        (Htyped2' : τ2 :: Γ # pc ⊔ₛ ℓ ⊢ₜ e2' : τ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : TSum τ1 τ2 @ ℓ)
        (IHtyped1 : τ1 :: Γ ⊨ e1 ≤ₗ e1' : τ)
        (IHtyped2 : τ2 :: Γ ⊨ e2 ≤ₗ e2' : τ)
        : Γ ⊨ Case e e1 e2 ≤ₗ Case e' e1' e2' : τ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind (CaseCtx _ _) w m y "#Hw" IHtyped.
    destruct τ as [ℓ' t]. destruct y.
    rewrite interp_sec_def interp_sum_def /=.
    destruct (bool_decide (⌊ ℓ' ⌋ₗ ρ ⊑ ζ)) eqn:Hflow2.
    - move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      move: Hflow2 => /bool_decide_eq_true_1 Hflow2.
      rewrite !bool_decide_eq_true_2 //; last by etransitivity.
      iDestruct "Hw" as (w1 w2) "[[% H2] | [% H2]]"; simplify_eq.
      + iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /= !up_env_subst.
        iApply (ic_wand_r ic_binary). iSplitL.
        { iApply (IHtyped1 _ _ ((w1,w2) :: vvs)). iFrame "#".
          iApply (interp_env_cons with "[$]"). }
        iIntros (?? []) "Hw /=".
        rewrite !interp_sec_def bool_decide_eq_true_2 //.
      + (* symmetric to previous case *)
        iApply ic_left_pure_step; [done|]; iNext.
        iApply ic_left_pure_step_index; [done|].
        rewrite -/of_val /= !up_env_subst.
        iApply (ic_wand_r ic_binary). iSplitL.
        { iApply (IHtyped2 _ _ ((w1,w2) :: vvs)). iFrame "#".
          iApply (interp_env_cons with "[$]"). }
        iIntros (?? []) "Hw /=".
        rewrite !interp_sec_def !bool_decide_eq_true_2 //.
    - move: Hflow2 => /bool_decide_eq_false_1 Hflow2.
      destruct (bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)) eqn:Hflow3.
      + move: Hflow3 => /bool_decide_eq_true_1 Hflow3.
        iDestruct "Hw" as (w1 w2) "[[% Hτ1] | [% Hτ2]]"; simplify_eq.
        * iApply ic_left_pure_step; [done|]; iNext.
          iApply ic_left_pure_step_index; [done|].
          rewrite -/of_val /=. rewrite !up_env_subst.
          iApply (ic_wand_r ic_binary). iSplitL.
          { iApply (IHtyped1 _ _ ((w1,w2) :: vvs)). iFrame "#".
            iApply (interp_env_cons with "[$]"). }
          iIntros (?? []) "Hw /=".
          rewrite !interp_sec_def !bool_decide_eq_false_2 //.
        * (* symmetric to previous case *)
          iApply ic_left_pure_step; [done|]; iNext.
          iApply ic_left_pure_step_index; [done|].
          rewrite -/of_val /= !up_env_subst.
          iApply (ic_wand_r ic_binary). iSplitL.
          { iApply (IHtyped2 _ _ ((w1,w2) :: vvs)). iFrame "#".
            iApply (interp_env_cons with "[$]"). }
          iIntros (?? []) "Hw /=".
          rewrite !interp_sec_def !bool_decide_eq_false_2 //.
      + iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[HΓl HΓr]".
        move: Hflow3 => /bool_decide_eq_false_1 Hflow3.
        move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
        rewrite !interp_un_sec_def !interp_un_sum_def.
        iDestruct "Hw" as "[[Hv | Hv]  [Hw | Hw]]";
          iDestruct "Hv" as (v') "[-> Hv]";
          iDestruct "Hw" as (w') "[-> Hw]";
          iDestruct (interp_un_env_cons with "[$Hv $HΓl]") as "#HΓl'";
          iDestruct (interp_un_env_cons with "[$Hw $HΓr]") as "#HΓr'".
        (* all four cases are symmetric *)
        * iApply ic_left_pure_step_index; [done|].
          iApply ic_left_pure_step; [done|]; iNext.
          rewrite -/of_val /= !up_env_subst.
          iApply ic_un_bi_lr. cbn.
          iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
          { iApply (fundamental_un with "HΓl'"); [done|].
            iPureIntro. by apply ord_join_neg_right. }
          iIntros (???) "#?".
          iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
          { iApply (fundamental_un with "HΓr'"); [done|].
            iPureIntro. by eapply ord_join_neg_right. }
          iIntros (???) "#?".
          rewrite !interp_sec_def bool_decide_eq_false_2; auto.
        * iApply ic_left_pure_step_index; [done|].
          iApply ic_left_pure_step; [done|]; iNext.
          rewrite -/of_val /= !up_env_subst.
          iApply ic_un_bi_lr; cbn.
          iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
          { iApply (fundamental_un with "HΓl'"); [done|].
            iPureIntro. by apply ord_join_neg_right. }
          iIntros (???) "#?".
          iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
          { iApply (fundamental_un with "HΓr'"); [done|].
            iPureIntro. by eapply ord_join_neg_right. }
          iIntros (???) "#?".
          rewrite !interp_sec_def bool_decide_eq_false_2; auto.
        * iApply ic_left_pure_step_index; [done|].
          iApply ic_left_pure_step; [done|]; iNext.
          rewrite -/of_val /= !up_env_subst.
          iApply ic_un_bi_lr; cbn.
          iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
          { iApply (fundamental_un with "HΓl'"); [done|].
            iPureIntro. by apply ord_join_neg_right. }
          iIntros (???) "#?".
          iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
          { iApply (fundamental_un with "HΓr'"); [done|].
            iPureIntro. by eapply ord_join_neg_right. }
          iIntros (???) "#?".
          rewrite !interp_sec_def bool_decide_eq_false_2; auto.
        * iApply ic_left_pure_step_index; [done|].
          iApply ic_left_pure_step; [done|]; iNext.
          rewrite -/of_val /= !up_env_subst.
          iApply ic_un_bi_lr; cbn.
          iApply (ic_wand_r (icd_step_fupd SI_left)). iSplitL.
          { iApply (fundamental_un with "HΓl'"); [done|].
            iPureIntro. by apply ord_join_neg_right. }
          iIntros (???) "#?".
          iApply (ic_wand_r (icd_step_fupd SI_right)). iSplitR.
          { iApply (fundamental_un with "HΓr'"); [done|].
            iPureIntro. by eapply ord_join_neg_right. }
          iIntros (???) "#?".
          rewrite !interp_sec_def bool_decide_eq_false_2; auto.
  Qed.

  Lemma bi_log_related_inl Γ e e' τ1 τ2
        (IHtyped : Γ ⊨ e ≤ₗ e' : τ1)
    : Γ ⊨ InjL e ≤ₗ InjL e' : TSum τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind InjLCtx w m y "#Hw" IHtyped.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    iModIntro. iEval (rewrite interp_sec_def).
    rewrite interp_sum_def bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_inr Γ e e' τ1 τ2
        (IHtyped : Γ ⊨ e ≤ₗ e' : τ2)
    : Γ ⊨ InjR e ≤ₗ InjR e' : TSum τ1 τ2 @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs Henv) "[#Hcoh #HΓ]".
    smart_ic_bind InjRCtx w m y "#Hw" IHtyped.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    iModIntro. iEval (rewrite interp_sec_def).
    rewrite interp_sum_def bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_subtype Γ e e' τ τ'
        (Hsub : τ' <:ₛ τ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : τ')
    : Γ ⊨ e ≤ₗ e' : τ.
  Proof.
    iIntros (Θ ρ vvs Henv) "[#Hcoh #HΓ]".
    iApply ic_wand_r; iSplitL; [iApply IHtyped; iFrame "#"|].
    iIntros (???) "? /=".
    by iApply interp_secsubtype.
  Qed.

  Lemma bi_log_related_alloc Γ pc e e' τ
        (Hflow : τ ↘ pc)
        (IHtyped : Γ ⊨ e ≤ₗ e' : τ)
    : Γ ⊨ Alloc e ≤ₗ Alloc e' : TRef τ @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs Henv) "[#Hcoh #HΓ]".
    smart_ic_bind AllocCtx v n x "#Hv" IHtyped.
    iApply (ic_fupd (icd_left SI_left SI_right)).
    iApply ic_un_bi_lr.
    iApply ((@ic_step_fupd_alloc _ secG_un_left) with "[//]").
    iNext. iIntros (l1) "Hl1".
    iApply ((@ic_step_fupd_alloc _ secG_un_right) with "[//]").
    iNext. iIntros (l2) "Hl2 /=".
    rewrite [⟦ TRef τ @ ⊥ₛ ⟧ₛ _ _ _]interp_sec_def interp_ref_def.
    rewrite bool_decide_eq_true_2; last auto.
    iExists (_,_). iSplitR; [done|].
    iApply inv_alloc. iNext.
    iExists _, _; cbn.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hv]") as "[? ?]".
    by iFrame; iFrame "#".
  Qed.

  Lemma bi_log_related_store Γ pc e1 e1' e2 e2' τ ℓ
        (Hflow : τ ↘ pc ⊔ₛ ℓ )
        (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : TRef τ @ ℓ)
        (IHtyped2 : Γ ⊨ e2 ≤ₗ e2' : τ)
    : Γ ⊨ Store e1 e2 ≤ₗ Store e1' e2' : TUnit @ ⊥ₛ.
  Proof.
    iIntros (Θ ρ vvs Henv) "[#Hcoh #Γ]".
    smart_ic_bind (StoreLCtx _) v n x "#Href" IHtyped1.
    smart_ic_bind (StoreRCtx _) v1' m y "#Hv'" IHtyped2.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hv']") as "#[? ?]".
    rewrite [⟦ TRef τ @ _ ⟧ₛ _ _ _]interp_sec_def interp_ref_def.
    case_bool_decide as Hflow'.
    - iDestruct "Href" as ([l1 l2]) "[% #Hinv]".
      destruct x, y as [v2' ?]. iSimplifyEq.
      iApply (ic_double_atomic_lr _ _ StronglyAtomic).
      iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
      iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
      iModIntro.
      iApply ((@ic_step_fupd_store _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@ic_fupd_store _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
      { iNext. iExists _,_. iFrame; iFrame "#". }
      rewrite [⟦ TUnit @ ⊥ₛ ⟧ₛ _ _ _]interp_sec_def interp_unit_def.
      rewrite bool_decide_eq_true_2; auto.
    - iDestruct "Href" as "[#Href1 #Href2]". destruct τ as [ℓ' t].
      rewrite !interp_un_sec_def !interp_un_ref_def /=.
      iDestruct "Href1" as (N1 l1 ->) "H1".
      iDestruct "Href2" as (N2 l2 ->) "H2".
      move: Hflow => /interp_label_join_ord_inv /(_ ρ) [Hflow1 Hflow2].
      rewrite bool_decide_eq_false_2; last by eapply ord_neg_left.
      iApply ic_un_bi_lr.
      iApply (ic_atomic ((icd_step_fupd SI_left)) _ StronglyAtomic _ ∅).
      iMod ("H1" with "[]") as "[Hl1 HcloseI1]"; first solve_ndisj.
      iDestruct "Hl1" as (w1) "[Hl1 #Hw1]".
      iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
      iModIntro.
      iApply ((@ic_step_fupd_store _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      rewrite !interp_un_sec_def.
      iMod "Hclose" as "_".
      iMod ("HcloseI1" with "[Hl1]") as "_".
      { iNext. iExists _. iFrame; iFrame "#". }
      iModIntro.
      iApply (ic_atomic ((icd_step_fupd SI_right)) _ StronglyAtomic _ ∅).
      iMod ("H2" with "[]") as "[Hl2 HcloseI2]"; first solve_ndisj.
      iDestruct "Hl2" as (w2) "[Hl2 #Hw2]".
      iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
      iModIntro.
      iApply ((@ic_step_fupd_store _ secG_un_right) with "[//]").
      iFrame. iIntros "!> Hl2".
      iMod "Hclose" as "_".
      iMod ("HcloseI2" with "[Hl2]") as "_".
      { iNext. iExists _. iFrame; iFrame "#". }
      rewrite [⟦ TUnit @ ⊥ₛ ⟧ₛ _ _ _]interp_sec_def interp_unit_def.
      rewrite bool_decide_eq_true_2; auto.
  Qed.

  Lemma bi_log_related_load Γ e e' τ τ' ℓ
        (Hflow : τ' ↘ ℓ)
        (Hsub : τ <:ₛ τ')
        (IHtyped : Γ ⊨ e ≤ₗ e' : TRef τ @ ℓ)
    : Γ ⊨ Load e ≤ₗ Load e' : τ'.
  Proof.
    iIntros (Θ ρ vvs ?) "[#Hcoh #HΓ]".
    smart_ic_bind LoadCtx v n x "#Href" IHtyped.
    rewrite interp_sec_def interp_ref_def.
    case_bool_decide as Hflow2.
    - iDestruct "Href" as ([l1 l2]) "[% #Hinv] /=".
      destruct x. iSimplifyEq.
      iApply (ic_double_atomic_lr _ _ StronglyAtomic).
      iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
      iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
      iMod fupd_intro_mask' as "Hclose"; first set_solver.
      iModIntro.
      iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@ic_fupd_load _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
      { iNext. iExists _,_. iFrame; iFrame "#". }
      by iApply interp_secsubtype.
    - iDestruct "Href" as "[#Href1 #Href2] /=".
      rewrite !interp_un_sec_def !interp_un_ref_def.
      destruct τ as [ℓ1 t1], τ' as [ℓ2 t2].
      iDestruct "Href1" as (N1 l1 ->) "#H1".
      iDestruct "Href2" as (N2 l2 ->) "#H2".
      move: Hflow => /interp_label_flowsto /(_ ρ) Hflow.
      iApply ic_un_bi_lr.
      iApply (ic_atomic ((icd_step_fupd SI_left)) _ StronglyAtomic _ ∅).
      case_bool_decide.
      + iMod ("H1" with "[]") as "Hl1"; first solve_ndisj.
        iDestruct "Hl1" as (w1) "[[Hl1 #Hw1] HcloseI1]".
        iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
        iModIntro.
        iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
        iFrame. iIntros "!> Hl1".
        iMod "Hclose" as "_".
        iMod ("HcloseI1" with "[Hl1]") as "_"; first eauto.
        iModIntro.
        iApply (ic_atomic ((icd_step_fupd SI_right)) _ StronglyAtomic _ ∅).
        iMod ("H2" with "[]") as "Hl2"; first solve_ndisj.
        iDestruct "Hl2" as (w2) "[[Hl2 #Hw2] HcloseI2]".
        iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
        iModIntro.
        iApply ((@ic_step_fupd_load _ secG_un_right) with "[//]").
        iFrame. iIntros "!> Hl2".
        iMod "Hclose" as "_".
        iMod ("HcloseI2" with "[Hl2]") as "_"; first eauto.
        iDestruct (interp_un_secsubtype with "Hw1") as "#Hw1'"; [done|].
        iDestruct (interp_un_secsubtype with "Hw2") as "#Hw2'"; [done|].
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
        by eapply ord_neg_left.
      + iMod ("H1" with "[]") as "[Hl1 HcloseI1]"; first solve_ndisj.
        iDestruct "Hl1" as (w1) "[Hl1 #Hw1]".
        iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
        iModIntro.
        iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
        iFrame. iIntros "!> Hl1".
        iMod "Hclose" as "_".
        iMod ("HcloseI1" with "[Hl1]") as "_"; first eauto.
        iModIntro.
        iApply (ic_atomic ((icd_step_fupd SI_right)) _ StronglyAtomic _ ∅).
        iMod ("H2" with "[]") as "[Hl2 HcloseI2]"; first solve_ndisj.
        iDestruct "Hl2" as (w2) "[Hl2 #Hw2]".
        iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
        iModIntro.
        iApply ((@ic_step_fupd_load _ secG_un_right) with "[//]").
        iFrame. iIntros "!> Hl2".
        iMod "Hclose" as "_".
        iMod ("HcloseI2" with "[Hl2]") as "_"; [auto|].
        iModIntro.
        iApply (interp_secsubtype (t1 @ ℓ1)); auto.
        rewrite interp_sec_def bool_decide_eq_false_2; auto.
  Qed.

  Lemma bi_log_related_pack Γ e e' τ t pc
        (Htyped1 : Γ # pc ⊢ₜ e : τ.|[t/])
        (Htyped2 : Γ # pc ⊢ₜ e' : τ.|[t/])
        (IHtyped : Γ ⊨ e ≤ₗ e' : τ.|[t/])
    : Γ ⊨ Pack e ≤ₗ Pack e' : TExist τ @ ⊥ₛ.
  Proof.
    iIntros (????) "#[Hcoh #HΓ]".
    smart_ic_bind PackCtx w n x "#Hv" IHtyped.
    iApply (ic_value (ic_binary)); umods.
    iApply (ic_value (icd_right SI_right)); umods.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hv]") as "#[Hw1 Hw2]".
    rewrite [⟦ TExist τ @ ⊥ₛ ⟧ₛ _ _ _]interp_sec_def interp_exist_def
            !interp_un_sec_def !interp_un_exist_def.
    rewrite bool_decide_eq_true_2; [|by apply ord_bottom].
    iModIntro. iModIntro.
    iExists (⟦ t ⟧ _ _), (⌊ t ₗ⌋ (projl _) _), (⌊ t ᵣ⌋ (projr _) _).
    repeat (iSplit; [iPureIntro; apply _|]). iSplit.
    { iIntros "!>" (?) "#?". iApply bi_subsume_un. iFrame "#". }
    iExists (_,_). do 2 (iSplit; [done|]).
    by iApply (interp_sec_type_subst_up _ []).
  Qed.

  Lemma bi_log_related_unpack Γ e1 e1' e2 e2' τ1 τ2 ℓ pc
      (Hflow : τ2 ↘ ℓ)
      (Htyped1 : τ1 :: (hsubst_sectype (ren (+1)) <$> Γ) # pc ⊔ₛ ℓ ⊢ₜ e2 : (hsubst_sectype (ren (+1)) τ2))
      (Htyped2 : τ1 :: (hsubst_sectype (ren (+1)) <$> Γ) # pc ⊔ₛ ℓ ⊢ₜ e2' : (hsubst_sectype (ren (+1)) τ2))
      (IHtyped1 : Γ ⊨ e1 ≤ₗ e1' : TExist τ1 @ ℓ)
      (IHtyped2 : τ1 :: (hsubst_sectype (ren (+1)) <$> Γ) ⊨ e2 ≤ₗ e2' : (hsubst_sectype (ren (+1)) τ2))
    : Γ ⊨ Unpack e1 e2 ≤ₗ Unpack e1' e2' : τ2.
  Proof.
    iIntros (????) "#[Hcoh HΓ]".
    smart_ic_bind (UnpackCtx _) w n x "#Hv" IHtyped1.
    rewrite interp_sec_def interp_exist_def.
    case_bool_decide as Hflow2.
    - destruct x; cbn.
      iDestruct "Hv" as (τR τi1 τi2) "(% & % & % & #Hrel & #Hv)".
      iDestruct "Hv" as ((?,?)) "(% & % & Hww)". simplify_eq. cbn.
      iApply ic_left_pure_step_index; [done|].
      iApply ic_left_pure_step; [done|]. iModIntro.
      rewrite !up_env_subst /=.
      iApply (ic_wand_r ic_binary); iSplitL.
      { iApply (IHtyped2 ((τR, (τi1, τi2)) :: _) _ ((_,_) :: _)). iSplit.
        - iApply big_sepL_cons; iFrame "#".
        - iApply interp_env_cons. iFrame "#".
          by iApply interp_bi_env_ren. }
      iIntros (???) "H /=".
      by iApply (interp_sec_type_weaken _ [] [_] _ 0).
    - destruct x. rewrite !interp_un_sec_def !interp_un_exist_def /=.
      iDestruct "Hv" as "[#Hv1 #Hv2]".
      iDestruct "Hv1" as (τi1) "(% & Hv1)". iDestruct "Hv1" as (v1) "(-> & Hv1)".
      iDestruct "Hv2" as (τi2) "(% & Hv2)". iDestruct "Hv2" as (v2) "(-> & Hv2)".
      iApply ic_left_pure_step_index; [done|].
      iApply ic_left_pure_step; [done|]. iModIntro. cbn.
      rewrite -/of_val !up_env_subst.
      iDestruct (interp_env_bi_un with "[$Hcoh $HΓ]") as "[HΓl HΓr]".
      iApply ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iDestruct (interp_un_env_ren with "HΓl") as "HΓl1".
        iDestruct (interp_un_env_cons with "[$Hv1 $HΓl1]") as "HΓl2".
        iApply ((fundamental_un _ _ _ _ Htyped1) with "HΓl2").
        iPureIntro. eapply ord_neg_left; [|done]. by apply ord_join_right. }
      iIntros (???) "#Hv1'".
      iApply ic_wand_r; iSplitL.
      { iDestruct (interp_un_env_ren with "HΓr") as "HΓr1".
        iDestruct (interp_un_env_cons with "[$Hv2 $HΓr1]") as "HΓr2".
        iApply ((fundamental_un _ _ _ _ Htyped2) with "HΓr2").
        iPureIntro. eapply ord_neg_left; [|done]. by apply ord_join_right. }
      iIntros (???) "#Hv2'".
      destruct τ2 as [ℓ2 t2].
      rewrite interp_sec_def.
      move: Hflow=> /interp_label_flowsto /(_ ρ) Hflow.
      move: (ord_neg_left _ _ _ Hflow Hflow2)=> ?.
      rewrite bool_decide_eq_false_2 //.
      iSplit; by iApply (interp_un_sec_type_weaken _ [] [_] _ 0).
  Qed.

  Lemma bi_log_related_fold Γ v v' τ
        (IHtyped : Γ  ⊨ v ≤ₗ v' : (τ.|[TRec τ/]))
    : Γ ⊨ Fold v ≤ₗ Fold v' : TRec τ @ ⊥ₛ.
  Proof.
    iIntros (????) "[#Hcoh #HΓ]".
    smart_ic_bind FoldCtx w n x "#Hv" IHtyped.
    iApply (ic_value (ic_binary)); umods.
    iApply (ic_value (icd_right SI_right)); umods. iModIntro.
    rewrite [⟦ TRec τ @ ⊥ₛ ⟧ₛ _ _ _]interp_sec_def interp_rec_def.
    rewrite bool_decide_eq_true_2; [|by apply ord_bottom].
    rewrite fixpoint_interp_rec1_eq /interp_rec1 /=.
    change (fixpoint _) with (⟦ TRec τ ⟧ Θ ρ).
    iModIntro. iExists (_,_). iSplit; [done|]. iModIntro.
    by iApply (interp_sec_type_subst_up _ []).
  Qed.

  Lemma bi_log_related_unfold Γ e e' τ ℓ
        (Hflow : τ.|[TRec τ/] ↘ ℓ)
        (IHtyped : Γ ⊨ e ≤ₗ e' : TRec τ @ ℓ)
    : Γ ⊨ Unfold e ≤ₗ Unfold e' : τ.|[TRec τ/].
  Proof.
    iIntros (????) "[#Hcoh #HΓ]".
    smart_ic_bind UnfoldCtx w n x "#Hw" IHtyped.
    rewrite [⟦ TRec τ @ _ ⟧ₛ _ _ _]interp_sec_def interp_rec_def.
    case_bool_decide as Hflow2.
    - destruct x. rewrite fixpoint_interp_rec1_eq /interp_rec1 /=.
      iDestruct "Hw" as ([w1 w2]) "[% #H]". simplify_eq.
      change (fixpoint _) with (⟦ TRec τ ⟧ Θ ρ).
      iApply ic_left_pure_step_index; [done|].
      iApply ic_left_pure_step; [done|]. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods.
      iModIntro.
      by iApply (interp_sec_type_subst_up _ []).
    - destruct x. rewrite !interp_un_sec_def !interp_un_rec_def.
      rewrite !fixpoint_interp_un_rec1_eq /interp_un_rec1 /=.
      iDestruct "Hw" as "[#Hv1 #Hv2]".
      iDestruct "Hv1" as (v1) "[-> Hv1]".
      iDestruct "Hv2" as (v2) "[-> Hv2]".
      replace (fixpoint _) with (⌊ TRec τ ₗ⌋ (projl Θ) ρ); [|done].
      replace (fixpoint _) with (⌊ TRec τ ᵣ⌋ (projr Θ) ρ); [|done].
      iApply ic_left_pure_step_index; [done|].
      iApply ic_left_pure_step; [done|]. iModIntro.
      rewrite -/of_val; cbn.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods.
      iModIntro. destruct τ.
      rewrite interp_sec_def /=. asimpl.
      move: Hflow=> /interp_label_flowsto /(_ ρ) Hflow.
      move: (ord_neg_left _ _ _ Hflow Hflow2)=> ?.
      rewrite bool_decide_eq_false_2 //.
      rewrite !interp_un_sec_def /=.
      iSplit; by iApply (interp_un_type_subst_up _ [] _ 0).
  Qed.

  Theorem binary_fundamental Γ pc e τ :
    Γ # pc ⊢ₜ e : τ → Γ ⊨ e ≤ₗ e : τ.
  Proof.
    induction 1.
    - apply bi_log_related_unit.
    - apply bi_log_related_bool.
    - apply bi_log_related_nat.
    - by apply bi_log_related_var.
    - by apply bi_log_related_lam.
    - by apply bi_log_related_binop.
    - by eapply bi_log_related_app.
    - by eapply bi_log_related_letin.
    - by eapply bi_log_related_seq.
    - by apply bi_log_related_tlam.
    - by eapply bi_log_related_tapp.
    - by apply bi_log_related_tllam.
    - by eapply bi_log_related_tlapp.
    - by eapply bi_log_related_if.
    - by apply bi_log_related_prod.
    - by eapply bi_log_related_proj1.
    - by eapply bi_log_related_proj2.
    - by apply bi_log_related_inl.
    - by apply bi_log_related_inr.
    - by eapply bi_log_related_case.
    - by eapply bi_log_related_alloc.
    - by eapply bi_log_related_store.
    - by eapply bi_log_related_load.
    - by eapply bi_log_related_pack.
    - by eapply bi_log_related_unpack.
    - by eapply bi_log_related_fold.
    - by eapply bi_log_related_unfold.
    - by eapply bi_log_related_subtype.
  Qed.

End fundamental.
