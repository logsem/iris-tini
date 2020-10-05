From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

(* OBS: high observer *)
Local Instance tpSecurityLatticeH : SecurityLattice tplabel := { ζ := H }.

(* This examples shows that it does not matter if we write H information to a L
     location if the observer is H---it is all the same for the observer. *)

(* low := !high *)
Definition prog_explicit_flow :=
  ($0 <- !$1)%E.

(* ... and the same is the case for implicit flows; the observer can see the
     secret, so both conditionals will always go into the same branch. *)

(* if !high then low := true else low := false *)
Definition prg_implicit_flow :=
  (if: !$1 then $0 <- true else $0 <- false)%E.

Section related.
  Context `{!secG Σ}.

  Lemma prg_high_to_low_bi_related :
    [TRef (TBool @ (LLabel L)) @ (LLabel L); TRef (TBool @ (LLabel H)) @ (LLabel L)] ⊨
     prog_explicit_flow ≤ₗ prog_explicit_flow : TUnit @ (LLabel L).
  Proof.
    iIntros (θ ρ vvs Hpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %?.
    do 2 (destruct vvs; [done|]).
    iDestruct (interp_env_cons with "Henv") as "[Hlow Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hhigh _]".
    rewrite !interp_sec_def.
    rewrite !bool_decide_eq_true_2 // !interp_ref_def.
    iDestruct "Hlow" as ([l1 l2]) "[-> #Hlow] /=".
    iDestruct "Hhigh" as ([l1' l2']) "[-> #Hhigh] /=".
    rewrite /interp_ref_inv /= !loc_to_val.
    iApply (mwp_left_strong_bind _ _ (fill [StoreRCtx _]) (fill [StoreRCtx _])); cbn.
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(l1',l2')) as "Hl" "HcloseI".
    iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
    iModIntro.
    iApply ((@mwp_step_fupd_load _ secG_un_left) with "[//]").
    iFrame. iIntros "!> Hl1".
    iApply ((@mwp_fupd_load _ secG_un_right) with "[//]").
    iFrame. iIntros "Hl2". ubools.
    rewrite bool_decide_eq_true_2 //=.
    iDestruct "Hτ" as (? b) "(-> & -> & ->)".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_true_2 //. eauto. }
    iModIntro.
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
    iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
    iModIntro.
    rewrite !bool_to_val.
    iApply (@mwp_step_fupd_store _ secG_un_left); [done|].
    iFrame. iIntros "!> Hl1".
    iApply (@mwp_fupd_store _ secG_un_right); [done|].
    iFrame. iIntros "Hl2".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
    iDestruct "Hτ" as (? b') "(-> & -> & ->)".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_true_2 //. eauto. }
    rewrite interp_sec_def interp_unit_def bool_decide_eq_true_2 //.
  Qed.

  Lemma prg_high_ctx_to_low :
    [TRef (TBool @ (LLabel L)) @ (LLabel L); TRef (TBool @ (LLabel H)) @ (LLabel L)] ⊨
    prg_implicit_flow ≤ₗ prg_implicit_flow : TUnit @ (LLabel L).
  Proof.
    iIntros (θ ρ vvs Hpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %?.
    do 2 (destruct vvs; [done|]).
    iDestruct (interp_env_cons with "Henv") as "[Hlow Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hhigh _]".
    rewrite !interp_sec_def.
    rewrite !bool_decide_eq_true_2 // !interp_ref_def.
    iDestruct "Hlow" as ([l1 l2]) "[-> #Hlow] /=".
    iDestruct "Hhigh" as ([l1' l2']) "[-> #Hhigh] /=".
    rewrite /interp_ref_inv /= !loc_to_val !bool_to_val.
    iApply (mwp_left_strong_bind _ _ (fill [IfCtx _ _]) (fill [IfCtx _ _])).
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(l1',l2')) as "Hl" "HcloseI".
    iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
    iModIntro.
    iApply ((@mwp_step_fupd_load _ secG_un_left) with "[//]").
    iFrame. iIntros "!> Hl1".
    iApply ((@mwp_fupd_load _ secG_un_right) with "[//]").
    iFrame. iIntros "Hl2".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
    iDestruct "Hτ" as (? b) "(-> & -> & ->)".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_true_2 //=. eauto. }
    iModIntro.
    destruct b.
    - iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iNext.
      iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
      iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
      iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
      iModIntro. rewrite !bool_to_val.
      iApply (@mwp_step_fupd_store _ secG_un_left); [done|].
      iFrame. iIntros "!> Hl1".
      iApply (@mwp_fupd_store _ secG_un_right); [done|].
      iFrame. iIntros "Hl2".
      rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
      iDestruct "Hτ" as (? b') "(-> & -> & ->)".
      iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
      { iNext. iExists _,_. iFrame. ubools.
        rewrite bool_decide_eq_true_2 //. eauto. }
      rewrite interp_sec_def interp_unit_def bool_decide_eq_true_2 //.
    - iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iNext.
      iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
      iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
      iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hτ) /=".
      iModIntro. rewrite !bool_to_val.
      iApply (@mwp_step_fupd_store _ secG_un_left); [done|].
      iFrame. iIntros "!> Hl1".
      iApply (@mwp_fupd_store _ secG_un_right); [done|].
      iFrame. iIntros "Hl2".
      rewrite interp_sec_def interp_bool_def bool_decide_eq_true_2 //=.
      iDestruct "Hτ" as (? b') "(-> & -> & ->)".
      iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
      { iNext. iExists _,_. iFrame. ubools.
        rewrite bool_decide_eq_true_2 //. eauto. }
      rewrite interp_sec_def interp_unit_def bool_decide_eq_true_2 //.
  Qed.

End related.
