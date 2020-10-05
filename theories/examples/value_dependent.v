From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

(* Output is a pair (is_secret, data) where the first projection denotes
   whether the second is secret or not. *)
Definition make_dep : expr :=
  λ: ref (#true, $0).

(* The idea here is that in [prog], [f] takes as input a reference to a pair of
   a boolean and a secret. However, it is not enough that [f] just treats the
   values as this.

   The soundness of [prog] relies on [f] keeping the classification invariant,
   e.g., it is *not* okay if [f] just flipped the boolean as this would mean
   that [prog] would be leaking the secret afterwards *)

(* λ f,
     let dep := make_dep secret in
     f dep ;;
     let tmp := !dep
     if (π₁ tmp) then 42 else (π₂ tmp)
 *)
Definition prog : expr :=
  λ:
    let: make_dep $1 in
    $1 $0 ;;
    let: ! $0 in
    if: Proj1 $0 then 42 else Proj2 $0.

Section proof.
  Context `{!secG Σ}.

  Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.

  Notation H := (LLabel H).
  Notation L := (LLabel L).

  Definition Ndep (ι1 ι2 : loc) := (nroot.@(ι1, ι2)).

  Definition dep_inv Θ ρ ι1 ι2 :=
    (∃ (b : bool) d1 d2, ι1 ↦ₗ (b, d1) ∗ ι2 ↦ᵣ (b, d2)
         ∗ ⟦ TNat @ (if b then H else L) ⟧ₛ Θ ρ (d1, d2))%I.

  Definition is_dep Θ ρ (p1 p2 : val) :=
    (∃ ι1 ι2, ⌜p1 = LocV ι1⌝ ∗ ⌜p2 = LocV ι2⌝ ∗ inv (Ndep ι1 ι2) (dep_inv Θ ρ ι1 ι2))%I.

  Lemma make_dep_spec (v1 v2 : val) Θ ρ :
    {{| ⟦ TNat @ H ⟧ₛ Θ ρ (v1, v2) |}}@{mwp_binary, (make_dep (# v2)) }
      make_dep (# v1)
    {{| v1 ; _ | v2 ; _, is_dep Θ ρ v1 v2 |}}.
  Proof.
    iIntros "_ !> Hnat". rewrite /make_dep.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    asimpl.
    iModIntro.
    iApply mwp_un_bi_lr. rewrite !bool_to_val !pair_to_val.
    iApply ((@mwp_step_fupd_alloc _ secG_un_left) with "[//]").
    iNext. iIntros (ι1) "Hι1".
    iApply mwp_fupd.
    iApply ((@mwp_step_fupd_alloc _ secG_un_right) with "[//]").
    iNext. iIntros (ι2) "Hι2"; cbn.
    iMod (inv_alloc (Ndep ι1 ι2) _ (dep_inv _ _ ι1 ι2) with "[-]") as "#Hinv".
    { iNext. iExists _,_,_. iFrame. }
    iModIntro. rewrite /is_dep.
    iExists _,_. auto.
  Qed.

  Definition is_closed (f : expr) := ∀ σ, f.[σ] = f.

  Lemma prog_related (f : expr) (fv v1 v2 : val) :
    IntoVal f fv →
    is_closed f →
    (∀ Θ ρ v1 v2,
    {{| is_dep Θ ρ v1 v2 |}}@{mwp_binary, f (# v2)}
        f (# v1)
    {{| _ ; _ | _ ; _, True |}}) →
    [TNat @ H] ⊨ prog f ≤ₗ prog f : TNat @ L.
  Proof.
    iIntros (Hfval Hfcl Hf Θ ρ vvs Hpers) "[Hcoh Henv]".
    iDestruct (interp_env_length with "Henv") as %Hlen.
    destruct vvs as [| []]; [done|]; clear Hlen.
    iDestruct (interp_env_cons with "Henv") as "[#Hn _]".
    asimpl. rewrite /interp_expr.
    rewrite lam_to_val !Hfcl -!Hfval.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    asimpl.
    iApply (mwp_left_strong_bind _ _ (fill [LetInCtx _]) (fill [LetInCtx _])); cbn.
    iModIntro.
    iApply (mwp_wand_r mwp_binary); iSplitL.
    { by iApply make_dep_spec. }
    iClear "Hn".
    iIntros (w1 ? [w2 ?]) "#Hdep"; cbn.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iNext; cbn. asimpl.
    rewrite !Hfval.
    iApply (mwp_left_strong_bind _ _ (fill [SeqCtx _]) (fill [SeqCtx _])); cbn.
    iApply (mwp_wand_r mwp_binary); iSplitL.
    { iApply (Hf with "[//] Hdep"). }
    iIntros (???) "_".
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iModIntro.
    iDestruct "Hdep" as (ι1 ι2) "(-> & -> & Hinv)". cbn.
    iApply (mwp_left_strong_bind _ _ (fill [LetInCtx _]) (fill [LetInCtx _])).
    iApply (mwp_double_atomic_lr _ _ StronglyAtomic).
    iInv (nroot.@(ι1,ι2)) as (b d1 d2) "(Hι1 & Hι2 & #Hι)" "HcloseI".
    iModIntro.
    iApply (@mwp_step_fupd_load _ secG_un_left); [done|].
    iFrame. iIntros "!> Hι1".
    iApply ((@mwp_fupd_load _ secG_un_right) with "[//]").
    iFrame. iIntros "Hι2".
    iMod ("HcloseI" with "[Hι1 Hι2 Hι]") as "_".
    { iNext. iExists _,_,_. iFrame. iFrame "#". }
    iModIntro. cbn.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iModIntro. asimpl.
    iApply (mwp_left_strong_bind _ _ (fill [IfCtx _ _]) (fill [IfCtx _ _])).
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value mwp_right); umods.
    do 2 iModIntro. rewrite bool_to_val.
    destruct b.
    - iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_value mwp_binary); umods.
      iApply (mwp_value mwp_right); umods.
      do 2 iModIntro. unats.
      rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2 //. eauto.
    - iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_value mwp_binary); umods.
      iApply (mwp_value mwp_right); umods.
      eauto.
  Qed.

End proof.
