From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas
     mwp_logrel_fupd ni_logrel_fupd_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

(* This is an implicit variation of [refs.v] where we leak (temporarily)
   information through an implicit flow but fix it before returning. *)
Definition prog : expr:=
  (if: !$1 = 42 then $0 <- 1 else $0 <- 0);; $0 <- 0.

Local Instance tpSecurityLatticeH : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

Section related.
  Context `{!secG Σ}.

  Lemma prog_related :
    [TRef (TNat @ L) @ L; TRef (TNat @ H) @ L] ⊨ prog ≤ₗ prog : TUnit @ L.
  Proof.
    iIntros (θ ρ vvs Hpers) "[#Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %H.
    do 2 (destruct vvs; [done|]); clear H.
    iDestruct (interp_env_cons with "Henv") as "[Hlow Henv']".
    iDestruct (interp_env_cons with "Henv'") as "[Hhigh _]".
    rewrite !interp_sec_def !bool_decide_eq_true_2 // !interp_ref_def.
    iDestruct "Hlow" as ([l1 l2]) "[-> #Hlow] /=".
    iDestruct "Hhigh" as ([h1 h2]) "[-> #Hhigh] /=".
    rewrite /interp_expr /=.
    iApply (mwp_left_strong_bind _ _ (fill [BinOpLCtx _ _; IfCtx _ _; SeqCtx _])
                                (fill [BinOpLCtx _ _; IfCtx _ _; SeqCtx _])); simpl.
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(h1,h2)) as "Hh" "Hclose !>".
    iDestruct "Hh" as (v1 v2) "(>Hh1 & >Hh2 & #Hv) /=".
    rewrite !loc_to_val.
    iApply (@mwp_step_fupd_load _ secG_un_left); [done|].
    iFrame. iIntros "!> Hh1".
    iApply (@mwp_fupd_load _ secG_un_right); [done|].
    iFrame. iIntros "Hh2 /=".
    iMod ("Hclose" with "[-]") as "_".
    { iExists _,_. iFrame. iFrame "#". }
    iModIntro.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hv]") as "[#Hv1 #Hv2] /=".
    rewrite ![⌊ TNat @ _ ⌋ₛ _ _]interp_un_sec_def !interp_un_nat_def.
    iDestruct "Hv1" as (n1) "->". iDestruct "Hv2" as (n2) "->".
    iApply (mwp_left_strong_bind _ _ (fill [IfCtx _ _; SeqCtx _])
                                (fill [IfCtx _ _; SeqCtx _])); simpl.
    rewrite !nat_to_val.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|]. simpl.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwpd_right SI_right)); umods.
    do 2 iModIntro.
    iApply ni_logrel_fupd_ni_logrel. iSplit.
    { iLeft. iIntros (σ) "Hσ".
      iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
      iModIntro. iPureIntro.
      eapply (fill_reducible [SeqCtx _]).
      apply head_prim_reducible.
      case_bool_decide; eexists [],_,_,[]; by econstructor. }
    iInv (nroot.@(l1,l2)) as "Hl" "HcloseI".
    iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & _) /=".
    do 2 iModIntro.
    iApply mwp_un_bi_fupd_lr.
    iApply (mwp_fupd_bind _ (fill [SeqCtx _])).
    case_bool_decide.
    - (* left then branch *)
      iApply mwp_fupd_pure_step; [done|].
      rewrite !loc_to_val !nat_to_val.
      iApply ((@mwp_fupd_store _ secG_un_left)); [done|].
      iFrame. iIntros "Hl1".
      iApply mwp_fupd_pure_step; [done|].
      iApply ((@mwp_fupd_store _ secG_un_left)); [done|].
      iFrame. iIntros "Hl1".
      case_bool_decide.
      + (* right then branch *)
        iApply (mwp_fupd_bind _ (fill [SeqCtx _])).
        iApply (mwp_fupd_pure_step); [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iApply mwp_fupd_pure_step; [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iMod ("HcloseI" with "[-]") as "_".
        { iExists _,_. iModIntro. iFrame. unats.
          rewrite [bool_decide (⌊ L ⌋ₗ ρ ⊑ ζ)]bool_decide_eq_true_2 //=; auto. }
        iIntros "!> /=".
        rewrite [⟦ () @ L ⟧ₛ _ _ _]interp_sec_def interp_unit_def
                bool_decide_eq_true_2 //.
      + (* right else branch *)
        iApply (mwp_fupd_bind _ (fill [SeqCtx _])).
        iApply (mwp_fupd_pure_step); [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iApply mwp_fupd_pure_step; [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iMod ("HcloseI" with "[-]") as "_".
        { iExists _,_. iModIntro. iFrame. unats.
          rewrite [bool_decide (⌊ L ⌋ₗ ρ ⊑ ζ)]bool_decide_eq_true_2 //=; auto. }
        iIntros "!> /=".
        rewrite [⟦ () @ L ⟧ₛ _ _ _]interp_sec_def interp_unit_def
                bool_decide_eq_true_2 //.
    - (* left else branch - identical to above *)
      iApply mwp_fupd_pure_step; [done|].
      rewrite !loc_to_val !nat_to_val.
      iApply ((@mwp_fupd_store _ secG_un_left)); [done|].
      iFrame. iIntros "Hl1".
      iApply mwp_fupd_pure_step; [done|].
      iApply ((@mwp_fupd_store _ secG_un_left)); [done|].
      iFrame. iIntros "Hl1".
      case_bool_decide.
      + (* right then branch *)
        iApply (mwp_fupd_bind _ (fill [SeqCtx _])).
        iApply (mwp_fupd_pure_step); [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iApply mwp_fupd_pure_step; [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iMod ("HcloseI" with "[-]") as "_".
        { iExists _,_. iModIntro. iFrame. unats.
          rewrite [bool_decide (⌊ L ⌋ₗ ρ ⊑ ζ)]bool_decide_eq_true_2 //=; auto. }
        iIntros "!> /=".
        rewrite [⟦ () @ L ⟧ₛ _ _ _]interp_sec_def interp_unit_def
                bool_decide_eq_true_2 //.
      + (* right else branch *)
        iApply (mwp_fupd_bind _ (fill [SeqCtx _])).
        iApply (mwp_fupd_pure_step); [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iApply mwp_fupd_pure_step; [done|].
        iApply ((@mwp_fupd_store _ secG_un_right)); [done|].
        iFrame. iIntros "Hl2".
        iMod ("HcloseI" with "[-]") as "_".
        { iExists _,_. iModIntro. iFrame. unats.
          rewrite [bool_decide (⌊ L ⌋ₗ ρ ⊑ ζ)]bool_decide_eq_true_2 //=; auto. }
        iIntros "!> /=".
        rewrite [⟦ () @ L ⟧ₛ _ _ _]interp_sec_def interp_unit_def
                bool_decide_eq_true_2 //.
  Qed.

End related.
