From iris.proofmode Require Import tactics.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.

(* if (!h) then 0 () else () *)
Definition prg_stuck :=
  (if: !$0 then true(Unit) (* stuck *) else ()%V)%E.

(* () *)
Definition prg_unit := ()%V.

Section related.
  Context `{!secG Σ}.

  Lemma prg_stuck_unit_bi_related :
    [TRef (TBool @ (LLabel H)) @ (LLabel L)] ⊨
    prg_stuck ≤ₗ prg_unit : TUnit @ (LLabel L).
  Proof.
    iIntros (Θ ρ vvs Henvpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %Heq.
    destruct vvs; [done|].
    iDestruct (interp_env_cons with "Henv") as "[#Href _]".
    rewrite !interp_sec_def !bool_decide_eq_true_2 // !interp_ref_def.
    iDestruct "Href" as ([l1 l2]) "[-> Href]".
    rewrite /interp_ref_inv /= !loc_to_val.
    iApply ic_un_bi_lr.
    iApply (ic_step_fupd_bind _ (fill [IfCtx _ _])).
    iApply (ic_atomic ((icd_step_fupd SI_left)) _ StronglyAtomic _ ∅).
    iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro.
    iDestruct "Hl" as (v1 v2) "(Hl1 & Hl2 & #Hb & _) /=".
    iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
    iFrame. iIntros "!> Hl1".
    rewrite interp_sec_def interp_bool_def bool_decide_eq_false_2 //.
    iDestruct "Hb" as "[Hb1 Hb2]".
    iMod "Hclose" as "_".
    iMod ("HcloseI" with "[Hl1 Hl2]") as "_".
    { iNext. iExists _,_. iFrame. ubools.
      rewrite bool_decide_eq_false_2 //. iSplit; eauto. }
    ubools. iDestruct "Hb1" as (b) "/= ->". iModIntro.
    destruct b.
    - iApply (ic_step_fupd_pure_step SI_left); [done|]. iModIntro.
      iApply ic_step_fupd_stuck; [done|].
      iIntros (σ) "Hσ /=".
      iMod (fupd_intro_mask' ⊤ ∅) as "_"; first done.
      do 2 iModIntro. iPureIntro.
      apply head_stuck_stuck.
      + split; [done|]. intros ???? Hs. inversion Hs.
      + apply ectxi_language_sub_redexes_are_values.
        intros [] ?; inversion 1; simpl; apply is_Some_alt=> //.
    - iApply (ic_step_fupd_pure_step SI_left); [done|]. iModIntro.
      iApply ic_value. umods. iModIntro.
      iApply (ic_value (icd_step_fupd SI_right)); umods. uunits.
      rewrite bool_decide_eq_true_2 //.
  Qed.

End related.
