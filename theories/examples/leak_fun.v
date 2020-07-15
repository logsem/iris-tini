From iris.proofmode Require Import tactics.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This example crystalizes how we allow leakage through termination. Under a
   termination-sensitive notion (e.g. SeLoC), the program is not secure because f
   and g can examine different termination behaviour. *)

(* (if (high) then f else g) () *)
Definition leak_funs : expr := ((if: $0 then $1 else $2) ()%V)%E.

Section related.
  Context `{!secG Σ}.

  Definition fg_type := (TArrow H (TUnit @ L) (TUnit @ L)) @ L.

  Lemma leak_funs_related :
    [TBool @ H; fg_type; fg_type] ⊨ leak_funs ≤ₗ leak_funs : TUnit @ L.
  Proof.
    iIntros (θ ρ vvs Hpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %H.
    do 3 (destruct vvs as [| []]; [done|]); clear H.
    iDestruct (interp_env_cons with "Henv") as "[Hb Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hf Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hg _]".
    rewrite !interp_sec_def /=.
    rewrite bool_decide_eq_false_2 // !bool_decide_eq_true_2 //.
    rewrite !interp_un_sec_def !interp_un_bool_def.
    iDestruct "Hb" as "[Hb1 Hb2]".
    iDestruct "Hb1" as (b1) "->". iDestruct "Hb2" as (b2) "->".
    rewrite !interp_arrow_def !interp_un_arrow_def.
    iDestruct "Hf" as "(#Hf & #Hf1 & #Hf2)".
    iDestruct "Hg" as "(#Hg & #Hg1 & #Hg2)".
    iApply ic_un_bi_lr.
    destruct b1.
    - iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply ic_value; umods. iModIntro.
      iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
      { iApply ("Hf1" $! UnitV); [|done]. uunits. by []. }
      iIntros (v ??). uunits. iIntros "->". rewrite bool_to_val.
      destruct b2.
      + iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
        iApply ic_step_fupd_pure_step; [done|]. iModIntro.
        iApply ic_value; umods. iModIntro.
        iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
        { iApply ("Hf2" $! UnitV); [|done]. uunits. by []. }
        iIntros (v ??) "/=". uunits. iIntros "->".
        rewrite bool_decide_eq_true_2 //.
      + iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
        iApply ic_step_fupd_pure_step; [done|]. iModIntro.
        iApply ic_value; umods. iModIntro.
        iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
        { iApply ("Hg2" $! UnitV); [|done]. uunits. by []. }
        iIntros (v ??) "/=". uunits. iIntros "->".
        rewrite bool_decide_eq_true_2 //.
    - iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply ic_value; umods. iModIntro.
      iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
      { iApply ("Hg1" $! UnitV); [|done]. uunits. by []. }
      iIntros (v ??) "/=". uunits. iIntros "->". rewrite bool_to_val.
      destruct b2.
      + iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
        iApply ic_step_fupd_pure_step; [done|]. iModIntro.
        iApply ic_value; umods. iModIntro.
        iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
        { iApply ("Hf2" $! UnitV); [|done]. uunits. by []. }
        iIntros (v ??) "/=". uunits. iIntros "->".
        rewrite bool_decide_eq_true_2 //.
      + iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
        iApply ic_step_fupd_pure_step; [done|]. iModIntro.
        iApply ic_value; umods. iModIntro.
        iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
        { iApply ("Hg2" $! UnitV); [|done]. uunits. by []. }
        iIntros (v ??) "/=". uunits. iIntros "->".
        rewrite bool_decide_eq_true_2 //.
  Qed.

End related.
