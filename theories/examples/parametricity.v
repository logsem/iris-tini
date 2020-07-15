From iris.proofmode Require Import tactics.
From IC.if_convergent Require Import IC_adequacy.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left.
From logrel_ifc.lambda_sec Require Import lattice notation fundamental_binary.

Definition SI Σ (x : gen_heapG loc val Σ) (σ : state) := gen_heap_ctx σ.

Definition SI_init σ Σ (x : gen_heapG loc val Σ) := gen_heap_ctx (hG := x) σ.

Instance SI_left_init_data σ `{!gen_heapPreG loc val Σ} : InitData (SI_init σ Σ).
Proof. apply gen_heap_init. Qed.

Section TP.
  Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
  Notation H := (LLabel H).
  Notation L := (LLabel L).

  (* Notice that the unary relation only says something when "in high contexts";
   the label for the lower bound on side effects has to be higher than the
   observer for us to use the result (c.f. the [⌊ pc ⌋ₗ ρ ⋢ ζ] condition in the
   unary expression relation). *)

  (* Also, remember that an TArrow/TForall/LForall with a [H] side-effect label
   can be executed in any context (in comparison to one with a [L] label that
   cannot be executed in a [H] context) *)

  (* (∀ᴴ α, ((α @ ℓ') →[H] (α @ ℓ'')) @ ℓ) @ ℓ implies [App e v] reduces to [v].*)
  Lemma identity_param e (v : val) σ ℓ ℓ' ℓ''
        (rd : Reds (e <_>ₜ (# v)) σ) :
    (∀ Σ (Hsg : secG_un Σ),
        [] # H ⊨ᵤ e : ((∀ₜ: H ; (($0 @ ℓ') →[H] ($0 @ ℓ'')) @ ℓ) @ ℓ)%type) →
    end_val rd = v.
  Proof.
    intros He.
    set (Σ := #[invΣ; gen_heapΣ loc val]).
    eapply (ic_step_fupd_adequacy (SI Σ) (SI_init σ Σ) _ _ _ (λ x _ , x = v)).
    rewrite /SI_init /SI /=.
    iIntros (?) "Hs".
    iModIntro; iFrame.
    specialize (He Σ (SecG_un _ _ (PIG_cnt _))).
    iPoseProof (He [] [] [] with "[] []") as "He".
    { iApply interp_un_env_nil. }
    { (* This is the first crucial point where the side-effect label of [TForall]
       has to be [H] *)
      done. }
    rewrite /=; asimpl.
    iApply (ic_step_fupd_bind _ (fill [TAppCtx; AppLCtx _])).
    iApply ic_wand_l; iFrame "He"; simpl.
    iIntros (w _ _) "#Hw". utforalls.
    iSpecialize ("Hw" $! (λ x, ⌜x = v⌝)%I with "[] []");
      first by iPureIntro; apply _.
    { (* The same is the case here, but for [TArrow] *)
      done. }
    iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
    iApply ic_wand_r; iSplitL.
    { iApply "Hw". }
    iIntros (u _ _) "#Hu /=".
    rewrite interp_un_sec_def interp_un_arrow_def /interp_un_expr.
    iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
    { iApply "Hu"; [|done]. rewrite interp_un_sec_def interp_un_tvar_def //. }
    iIntros (???). by utvars.
  Qed.

  (* (∀ᴴ α, (α @ ℓ')) @ ℓ is is only inhabited by diverging functions (in a high pc) *)
  Lemma empty_type_param e (v : val) σ ℓ ℓ'
        (rd : Reds (e <_>ₜ) σ) :
    (∀ Σ (Hsg : secG_un Σ),
        [] # H ⊨ᵤ e : ((∀ₜ: H ; ($0 @ ℓ')) @ ℓ)%type)  →
    False.
  Proof.
    intros He.
    set (Σ := #[invΣ; gen_heapΣ loc val]).
    eapply (ic_step_fupd_adequacy (SI Σ) (SI_init σ Σ) _ _ _ (λ _ _ , False)); [|done].
    rewrite /SI_init /SI /=.
    iIntros (?) "Hs".
    iModIntro; iFrame.
    specialize (He Σ (SecG_un _ _ (PIG_cnt _))).
    iPoseProof (He [] [] [] with "[] []") as "He".
    { iApply interp_un_env_nil. }
    { done. }
    rewrite /=; asimpl.
    iApply (ic_step_fupd_bind _ (fill [TAppCtx])).
    iApply ic_wand_l; iFrame "He"; simpl.
    iIntros (w _ _) "#Hw". utforalls.
    iSpecialize ("Hw" $! (λ _, False)%I with "[] []");
      first by iPureIntro; apply _.
    { done. }
    iApply "Hw".
  Qed.

  (* (∀ᴴ α, (αᴴ →[H] αᴸ) @ L) @ L is only inhabited by diverging functions *)
  Lemma no_high_to_low e (v : val) σ
        (rd : Reds (e <_>ₜ (# v)) σ) :
    (∀ Σ (Hsg : secG Σ),
        [] ⊨ e ≤ₗ e : ((∀ₜ: H; (($0 @ H) →[H] ($0 @ L)) @ L) @ L)%type) →
    False.
  Proof.
    intros He.
    set (Σ := #[invΣ; gen_heapΣ loc val]).
    eapply (ic_left_adequacy
              (SI Σ) (SI Σ) (SI_init σ Σ) (SI_init σ Σ) _ _ _ _ _ (λ x _ y _, False)); [|done|done].
    rewrite /SI_init /SI /=.
    iIntros ([? [leftG rightG]]).
    rewrite /SI_init /SI /=.
    iIntros "[Hl Hr]".
    iModIntro. iFrame.
    specialize (He Σ (SecG _ _ leftG rightG)).
    iPoseProof (He [] [] [] with "[]") as "He".
    { rewrite /env_coherent. iSplitL; [done|]. iApply interp_env_nil. }
    rewrite /=; asimpl.
    iApply (ic_left_strong_bind _ _ (fill [TAppCtx; AppLCtx _]) (fill [TAppCtx; AppLCtx _])). cbn.
    iApply (ic_wand_r (icd_left _ _)). iSplitL.
    { iApply "He". }
    iClear "He".
    iIntros (w ??) "#Hw /=". utforalls.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hw" as "#(#Hw & Hw1 & Hw2)".
    iSpecialize ("Hw" $! (λ _, False)%I (λ _, True)%I (λ _, True)%I).
    iApply (ic_left_strong_bind _ _ (fill [AppLCtx _]) (fill [AppLCtx _])).
    iApply ic_wand_r; iSplitL.
    { iApply "Hw".
      - iPureIntro; intros []; apply _.
      - iPureIntro. apply _.
      - iPureIntro. apply _.
      - iModIntro. iIntros ([]). eauto. }
    iClear "Hw Hw1 Hw2".
    iIntros (u ??) "Hu /=". uarrows.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hu" as "#(#Hu & _)".
    iApply (ic_wand_r (icd_left _ _)); iSplitL.
    { iApply ("Hu" $! (_, _)). utvars. rewrite bool_decide_eq_false_2 //. }
    iIntros (???) "? /=". utvars.
    rewrite bool_decide_eq_true_2 //.
  Qed.

End TP.

Section arbitrary.
  Context `{SecurityLattice label}.

  (* It is in general not sound to have a "suspendend" computation (arrows &
     foralls) where the claimed lower bound on its side effects are lower than
     the label of the computation value itself (e.g., the lambda).

     Take

       [λ x. e1 : (τ →[L] τ') @ H]

     This function could be invoked in a high context, but if [e1] has low side-effects,
     this could porentially leak secrets.

       [if (h) then (λ x. e1) t else ()]

   *)

  (* (∀^ℓ1 α, ((α @ ℓ) →[ℓ2] (α @ ℓ)) @ ℓ3) ℓ4 *)
  Lemma identity_param_bi e (v : val) σ ℓ ℓ1 ℓ2 ℓ3 ℓ4
        (rd : Reds (e <_>ₜ (# v)) σ) :
    ⌊ ℓ3 ⌋ₗ [] ⊑ ⌊ ℓ2 ⌋ₗ [] → (* the label of the arrow should not be greather than its side effects *)
    ⌊ ℓ4 ⌋ₗ [] ⊑ ⌊ ℓ2 ⌋ₗ [] → (* the label of the forall should not be greater than the arrow's side effects *)
    ⌊ ℓ4 ⌋ₗ [] ⊑ ⌊ ℓ1 ⌋ₗ [] → (* the label of the forall should not be greather than its side effects *)
    (∀ Σ (Hsg : secG Σ),
        [] ⊨ e ≤ₗ e : ((∀ₜ: ℓ1; (($0 @ ℓ) →[ℓ2] ($0 @ ℓ)) @ ℓ3) @ ℓ4)%type) →
    end_val rd = v.
  Proof.
    intros Hflow1 Hflow2 Hflow3 He.
    set (Σ := #[invΣ; gen_heapΣ loc val]).
    eapply (ic_left_adequacy
              (SI Σ) (SI Σ) (SI_init σ Σ) (SI_init σ Σ) _ _ _ _ _ (λ x _ y _, x = v)); [|done].
    rewrite /SI_init /SI /=.
    iIntros ([? [leftG rightG]]).
    rewrite /SI_init /SI /=.
    iIntros "[Hl Hr]".
    iModIntro. iFrame.
    specialize (He Σ (SecG _ _ leftG rightG)).
    iPoseProof (He [] [] [] with "[]") as "He".
    { rewrite /env_coherent. iSplitL; [done|]. iApply interp_env_nil. }
    rewrite /=; asimpl.
    iApply (ic_left_strong_bind _ _ (fill [TAppCtx; AppLCtx _]) (fill [TAppCtx; AppLCtx _])). cbn.
    iApply (ic_wand_r (icd_left _ _)). iSplitL.
    { iApply "He". }
    iClear "He".
    iIntros (w ??) "#Hw /=". utforalls.
    case_bool_decide.
    - iDestruct "Hw" as "#(#Hw & Hw1 & Hw2)".
      iSpecialize ("Hw" $! (λ '(x, y), ⌜x = v⌝ ∧ ⌜y = v⌝)%I (λ x, ⌜x = v⌝)%I (λ x, ⌜x = v⌝)%I).
      iApply (ic_left_strong_bind _ _ (fill [AppLCtx _]) (fill [AppLCtx _])).
      iApply ic_wand_r; iSplitL.
      { iApply "Hw".
        - iPureIntro; intros []; apply _.
        - iPureIntro. apply _.
        - iPureIntro. apply _.
        - iModIntro. iIntros ([]). eauto. }
      iClear "Hw Hw1 Hw2".
      iIntros (u ??) "Hu /=". uarrows.
      case_bool_decide as Heq.
      + iDestruct "Hu" as "#(#Hu & _)".
        iApply (ic_wand_r (icd_left _ _)); iSplitL.
        { iApply ("Hu" $! (_, _)). utvars. case_bool_decide; eauto. }
        iIntros (???) "/=". utvars. case_bool_decide.
        { by iIntros "[-> _]". }
        by iIntros "/= [-> _]".
      + iDestruct "Hu" as "(#Hu1 & #Hu2) /=".
        iApply ni_logrel_lemmas.ic_un_bi_lr.
        iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
        { iApply "Hu1"; [by utvars|]. iPureIntro. by eapply (ord_neg_left _ _ _ Hflow1). }
        iIntros (???) "/=". utvars. iIntros "->".
        iApply (ic_wand_r (icd_step_fupd _)). iSplitL.
        { iApply "Hu2"; [by utvars|]. iPureIntro. by eapply (ord_neg_left _ _ _ Hflow1). }
        by iIntros (???) "?".
    - iDestruct "Hw" as "[#Hw1 #Hw2]".
      iApply (ic_left_strong_bind _ _ (fill [AppLCtx _]) (fill [AppLCtx _])). cbn.
      iSpecialize ("Hw1" $! (λ x, ⌜x = v⌝)%I with "[]"); first (iPureIntro; apply _).
      iSpecialize ("Hw2" $! (λ x, ⌜x = v⌝)%I with "[]"); first (iPureIntro; apply _).
      iApply ni_logrel_lemmas.ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iApply "Hw1". iPureIntro. by eapply ord_neg_left. }
      iIntros (u1 ??) "#Hu1". cbn.
      iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
      { iApply "Hw2". iPureIntro. by eapply ord_neg_left. }
      iIntros (u2 ??) "#Hu2". uarrows.
      iApply ni_logrel_lemmas.ic_un_bi_lr.
      iApply ic_wand_r; iSplitL.
      { iApply "Hu1"; [by utvars|]. iPureIntro. by eapply ord_neg_left. }
      iIntros (???). utvars. iIntros "->".
      iApply ic_wand_r; iSplitL.
      { iApply "Hu2"; [by utvars|]. iPureIntro. by eapply ord_neg_left. }
      iIntros (???). utvars. by iIntros "->".
  Qed.

End arbitrary.
