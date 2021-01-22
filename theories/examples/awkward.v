From iris.algebra Require Import csum agree excl.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* The classical 'awkward' example; the inner closure is *not* syntactically
   well-typed at 'awk_type` as the local reference will have to be typed at [H]
   as we initialize it with a [H] value. *)

(* let awk v =
      let x = ref v
      in λ f, x <- 1; f (); !x
 *)
Definition awk : val :=
  λ:
    let: ref $0 in
    λ: $1 <- #1 ;;
    $0 ()%V ;;
    !($1).

Definition awk_type : type :=
  (TNat @ H) →[H] ((((TUnit @ L →[L] TUnit @ L) @ L) →[L] (TNat @ L)) @ L).

Definition oneshotR := csumR (exclR unitR) (agreeR unitR).
Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Section oneshot.
  Context `{!oneshotG Σ}.

  Definition pending γ := own γ (Cinl (Excl ())).
  Definition shot γ := own γ (Cinr (to_agree ())).
  Lemma new_pending : ⊢ |==> ∃ γ, pending γ.
  Proof. by apply own_alloc. Qed.
  Lemma shoot γ : pending γ ==∗ shot γ.
  Proof.
    apply own_update.
    intros n [f |]; simpl; eauto.
    destruct f; simpl; try by inversion 1.
  Qed.
  Definition shootN := nroot .@ "shootN".
  Lemma shot_not_pending γ :
    shot γ -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.
End oneshot.

Section related_un.
  Context `{!oneshotG Σ}.
  Context (secG : secG_un Σ).

  Lemma awkward_un Δ ρ :
    env_Persistent Δ →
    ⊢ ⌊ awk_type @ L ⌋ₛ Δ ρ awk.
  Proof.
    move=> ?. uarrows. rewrite /interp_un_expr.
    iIntros "!>" (n) "Hn %".
    iApply mwp_step_fupd_pure_step; [done|].
    iModIntro.
    iApply (mwp_step_fupd_bind _ (fill [LetInCtx _])); cbn.
    iApply (mwp_step_fupd_alloc with "[//]").
    iIntros "!>" (l) "Hl".
    iApply mwp_step_fupd_pure_step; [done|]. asimpl.
    iModIntro.
    iMod new_pending as (γ) "Hγ".
    iMod (inv_alloc shootN _ ((∃ v, pending γ ∗ l ↦ v) ∨ (shot γ ∗ l ↦ (NatV 1))%I)
            with "[Hl Hγ]") as "#Hinv".
    Unshelve. 
    { iNext. iLeft. iExists _. by iFrame. }
    iApply (mwp_value (mwpd_step_fupd SI)); umods.
    uarrows. iIntros "!> !>" (?) "_ %Hflow".
    by destruct Hflow.
  Qed.
End related_un.

Section related.
  Context `{!secG Σ}.
  Context `{!oneshotG Σ}.

  Lemma awkward_related :
    [] ⊨ #awk ≤ₗ #awk : awk_type @ L.
  Proof.
    iIntros (Θ ρ vvs Henv) "[#Hcoh _]".
    iApply (mwp_value mwp_binary). umods.
    iApply (mwp_value (mwpd_right SI_right)). umods.
    iIntros "!>". asimpl. uarrows. cbn.
    rewrite bool_decide_eq_true_2 //. uarrows.
    iSplit; last first.
    { iSplit; iApply awkward_un. }
    iIntros "!>" ([w1 w2]). unats.
    rewrite bool_decide_eq_false_2 //.
    iIntros "[Hw1 Hw2]".
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    asimpl. iModIntro.
    iApply (mwp_left_strong_bind _ _ (fill [LetInCtx _]) (fill [LetInCtx _])); cbn.
    iApply mwp_un_bi_lr.
    iApply ((@mwp_step_fupd_alloc _ secG_un_left) with "[//]").
    iIntros "!>" (l1) "Hl1".
    iApply ((@mwp_step_fupd_alloc _ secG_un_right) with "[//]").
    iNext. iIntros (l2) "Hl2". cbn.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwpd_right SI_right)); umods.
    iNext.
    iMod new_pending as (γ) "Hγ".
    iMod (inv_alloc shootN _ ((∃ v1 v2, pending γ ∗ l1 ↦ₗ v1 ∗ l2 ↦ᵣ v2)
                              ∨ (shot γ ∗ l1 ↦ₗ 1 ∗ l2 ↦ᵣ 1))%I
            with "[Hl1 Hl2 Hγ]") as "#Hinv".
    { iNext. iLeft. iExists _,_. by iFrame. }
    iModIntro. asimpl.
    rewrite interp_sec_def interp_arrow_def.
    rewrite !bool_decide_eq_true_2 //.
    iSplit; last first.
    { uarrows. iSplit; by iIntros "!>" (?) "_ %". }
    iIntros "!>" ([v1 v2]). uarrows.
    rewrite bool_decide_eq_true_2 //.
    iIntros "(#Hf & #Hf1 & #Hf2)".
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iModIntro. asimpl.
    iApply (mwp_left_strong_bind _ _ (fill [SeqCtx _]) (fill [SeqCtx _])); cbn.
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv shootN as "HN" "Hcl". iModIntro.
    iDestruct "HN" as "[HN|[#Hγ [>Hl1 >Hl2]]]".
    - iDestruct "HN" as (u1 u2) "[>Hγ [>Hl1 >Hl2]]".
      rewrite !loc_to_val !nat_to_val.
      iApply ((@mwp_step_fupd_store _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@mwp_fupd_store _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod (shoot with "Hγ") as "#Hγ".
      iMod ("Hcl" with "[-]") as "_".
      { iRight. by iFrame. }
      iModIntro.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_left_strong_bind _ _ (fill [SeqCtx _]) (fill [SeqCtx _])); cbn.
      iApply (mwp_wand_r mwp_binary). iSplitL.
      { iApply ("Hf" $! (UnitV, UnitV)). uunits.
        rewrite bool_decide_eq_true_2 //. }
      iIntros "!>" (???) "#Hτ".
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iNext.
      iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
      iInv shootN as "HN" "Hcl". iModIntro.
      iDestruct "HN" as "[HN|[_ [>Hl1 >Hl2]]]".
      { iDestruct "HN" as (??) "[>Hγ' [>Hl1 >Hl2]]".
        iDestruct (shot_not_pending with "Hγ Hγ'") as "[]". }
      iApply ((@mwp_step_fupd_load _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@mwp_fupd_load _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod ("Hcl" with "[-]") as "_".
      { iRight. by iFrame. }
      iModIntro. cbn. unats.
      rewrite bool_decide_eq_true_2 //. eauto.
    - rewrite !loc_to_val !nat_to_val.
      iApply ((@mwp_step_fupd_store _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@mwp_fupd_store _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod ("Hcl" with "[-]") as "_".
      { iRight. by iFrame. }
      iModIntro.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_left_strong_bind _ _ (fill [SeqCtx _]) (fill [SeqCtx _])); cbn.
      iApply (mwp_wand_r mwp_binary). iSplitL.
      { iApply ("Hf" $! (UnitV, UnitV)).
        uunits. rewrite bool_decide_eq_true_2 //. }
      iIntros "!>" (???) "#Hτ".
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iNext.
      iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
      iInv shootN as "HN" "Hcl". iModIntro.
      iDestruct "HN" as "[HN|[_ [>Hl1 >Hl2]]]".
      { iDestruct "HN" as (??) "[>Hγ' [>Hl1 >Hl2]]".
        iDestruct (shot_not_pending with "Hγ Hγ'") as "[]". }
      iApply ((@mwp_step_fupd_load _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      iApply ((@mwp_fupd_load _ secG_un_right) with "[//]").
      iFrame. iIntros "Hl2".
      iMod ("Hcl" with "[-]") as "_".
      { iRight. by iFrame. }
      iModIntro. cbn. unats.
      rewrite bool_decide_eq_true_2 //. eauto.
  Qed.

End related.
