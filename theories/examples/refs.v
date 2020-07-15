From iris.proofmode Require Import tactics.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas
     IC_logrel_fupd ni_logrel_fupd_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

(* This examples exploits that we do not have concurrency and can temporarily
     use the external (L-)reference for storing secret (H-)information. *)

(* let temp := !low
     in low := !high;
        low := temp
 *)
Definition high_in_low_temp :=
  (let: !$0 in $1 <- !$2 ;; $1 <- $0)%E.

Local Instance tpSecurityLatticeH : SecurityLattice tplabel := { ζ := L }.

Section related.
  Context `{!secG Σ}.

  Lemma prg_high_to_low_bi_related :
    [TRef (TBool @ (LLabel L)) @ (LLabel L); TRef (TBool @ (LLabel H)) @ (LLabel L)] ⊨
     high_in_low_temp ≤ₗ high_in_low_temp : TUnit @ (LLabel L).
  Proof.
    iIntros (θ ρ vvs Hpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %H.
    do 2 (destruct vvs; [done|]); clear H.
    iDestruct (interp_env_cons with "Henv") as "[Hlow Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hhigh _]".
    rewrite !interp_sec_def !bool_decide_eq_true_2 // !interp_ref_def.
    iDestruct "Hlow" as ([l1 l2]) "[-> #Hlow] /=".
    iDestruct "Hhigh" as ([l1' l2']) "[-> #Hhigh] /=".
    asimpl. rewrite /interp_ref_inv /=.
    iApply (ic_left_strong_bind _ _ (fill [LetInCtx _]) (fill [LetInCtx _])); cbn.
    iApply (ic_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
    iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
    iModIntro.
    iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
    iFrame. iIntros "!> Hl1".
    iApply ((@ic_fupd_load _ secG_un_right) with "[//]").
    iFrame. iIntros "Hl2".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
    iDestruct "Hτ" as (? b) "(-> & -> & ->)".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_true_2 //=. eauto. }
    iModIntro.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro. rewrite /= !loc_to_val.
    iApply (ic_left_strong_bind _ _ (fill [(StoreRCtx _) ; (SeqCtx _)])
                                    (fill [(StoreRCtx _) ; (SeqCtx _)])); cbn.
    iApply (ic_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(l1',l2')) as "Hl" "HcloseI".
    iDestruct "Hl" as (v1 v2) "(Hl1' & Hl2' & #Hτ) /=".
    iModIntro.
    iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
    iFrame. iIntros "!> Hl1'".
    iApply ((@ic_fupd_load _ secG_un_right) with "[//]").
    iFrame. iIntros "Hl2'".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_false_2 //=.
    iDestruct "Hτ" as "[Hτ1 Hτ2]".
    iMod ("HcloseI" with "[Hl1' Hl2']") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_false_2 //=. iSplit; eauto. }
    iModIntro.
    iApply ni_logrel_fupd_ni_logrel. iSplit.
    { iLeft. iIntros (σ) "Hσ".
      iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
      iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
      iDestruct "Hl" as (??) "(>Hl1 & >Hl2 & _) /=".
      iDestruct (gen_heap_valid with "Hσ Hl1") as "%".
      iModIntro. iPureIntro.
      rewrite !loc_to_val.
      eapply (fill_reducible [SeqCtx _]).
      apply head_prim_reducible.
      eexists [],_,_,[]. econstructor; [done|].
      rewrite H1; by eexists. }
    iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
    do 2 iModIntro.
    iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & #Hτ) /=".
    iApply ic_un_bi_fupd_lr.
    iApply (ic_fupd_bind _ (fill [SeqCtx _])); simpl.
    iApply ((@ic_fupd_store _ secG_un_left) with "[//]").
    iFrame. iIntros "Hl1".
    iApply ic_fupd_pure_step; [done|].
    rewrite loc_to_val bool_to_val.
    iApply ((@ic_fupd_store _ secG_un_left) with "[//]").
    iFrame; iIntros "Hl1".
    iApply (ic_fupd_bind _ (fill [SeqCtx _])); simpl.
    iApply ((@ic_fupd_store _ secG_un_right) with "[//]").
    iFrame. iIntros "Hl2".
    iApply ic_fupd_pure_step; [done|].
    rewrite loc_to_val bool_to_val.
    iApply ((@ic_fupd_store _ secG_un_right) with "[//]").
    iFrame; iIntros "Hl2".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_true_2 //=. eauto. }
    rewrite !interp_sec_def bool_decide_eq_true_2 // interp_unit_def //.
  Qed.

End related.