From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This is morally the same example as as in [value_dependent.v] but we use an
   existential pack to enforce the invariant that we in the other example have
   users prove. *)
Definition get : val :=
  λ: let: ! $0 in
     if: Proj1 $0 then InjL (Proj2 $0) else InjR (Proj2 $0).
Definition setL : val :=
  λ: (Proj1 $0) <- (#false, (Proj2 $0)).
Definition setH : val :=
  λ: (Proj1 $0) <- (#true, (Proj2 $0)).
Definition make_dep : val :=
  λ: pack: (ref (#true, $0), (# get), (# setL), (# setH)).

(* (αᴸ →ᴴ (Natᴴ + Natᴸ)ᴸ)ᴸ *)
Definition get_typ : sectype :=
  (($0 @ L) →[H] (((TNat @ H) + (TNat @ L)) @ L)) @ L.

(* ((αᴸ × Natᴸ)ᴸ →ᴸ Unitᴸ)ᴸ *)
Definition setL_typ : sectype :=
  ((($0 @ L) * (TNat @ L)) @ L →[L] (() @ L)) @ L.

(* ((αᴸ × Natᴴ)ᴸ →ᴸ Unitᴸ)ᴸ *)
Definition setH_typ : sectype :=
  ((($0 @ L) * (TNat @ H)) @ L →[L] (() @ L)) @ L.

(* Note that the side-effect labels of [setL] and [setH] are [L]; it is crucial
   that these functions are not called in a high context due to their low-
   observable side-effects.

   Consider the example below where [v : αᴸ]:

     if my_other_secret
     then setL (v,42)
     else setL (v,43)

   The result of calling [get v] after this expression will vary based on
   [my_other_secret] and hence leak its contents implicitly. Similarly,
   for [setH]:

     setL (v, 1) ;;
     (if my_other_secret
      then setH (v, secret)
      else ());;
     get v

   Whether [get v] returns [InjL _] or [InjR _] will reveal [my_other_secret].

   In the pure example (see [value_dependent_pack_no_ref.v]) we do not have
   side-effecs (hence the lower-bound label can be [H]). If considering the
   example above in that setting, both branches are forced to be typed as [H]
   such that the type of the return values properly propagate that they
   depend on secrets. *)

(* ∃ α,
    (αᴸ *
    (αᴸ →ᴴ (Natᴴ + Natᴸ)ᴸ)ᴸ *
   ((αᴸ × Natᴸ)ᴸ →ᴸ Unitᴸ)ᴸ *
   ((αᴸ × Natᴴ)ᴸ →ᴸ Unitᴸ)ᴸ)ᴸ
 *)
Definition dep_typ : type :=
  ∃: ((((((($0 @ L) * get_typ) @ L) * setL_typ) @ L) * setH_typ) @ L).

Definition make_dep_typ : type :=
  ((TNat @ H) →[L] (dep_typ @ L)).

(* λ make_dep, secret, f,
     let dep := make_dep secret in
     f dep ;;
     unpack dep in
       let v := π1 (π1 (π1 dep)) in
       let get := π2 (π1 (π1 dep)) in
       match (get v) with
         InjL _ => 42
       | InjR x => x
       end
 *)
Definition client : expr :=
  λ: λ: λ:
    let: $2 $1 in
    $1 $0 ;;
    unpack: $0 in
      let: Proj1 (Proj1 (Proj1 $0)) in (* αᴸ *)
      let: Proj2 (Proj1 (Proj1 $1)) in (* get *)
      match: $0 $1 with
        InjL => 42
      | InjR => $0
      end.

Definition client_type_inner : type :=
  ((TNat @ H) →[L] (((dep_typ @ L →[L] (TUnit @ L)) @ L) →[L] (TNat @ L)) @ L).

(* make_dep_typ →ᴸ Natᴴ →ᴸ (dep_typ →ᴸ Unitᴸ) →ᴸ Natᴸ *)
Definition client_type : type :=
  (make_dep_typ @ L →[L] client_type_inner @ L)%type.

Lemma client_typed :
  [] # L ⊢ₜ client : client_type @ L.
Proof.
  rewrite /client /client_type.
  do 3 constructor.
  eapply (LetIn_typed _ _ _ _ (dep_typ @ L)).
  - rewrite /make_dep /make_dep_typ.
    econstructor; try by constructor.
  - econstructor.
    { econstructor; try by constructor. }
    econstructor; try by constructor.
    econstructor.
    { by do 5 econstructor. }
    econstructor.
    { by do 5 econstructor. }
    econstructor; try by constructor.
    econstructor; try by constructor.
Qed.


(************************ Proofs ************************)
Definition Ndep : namespace := nroot.@"dep".

Section un_defs.
  Context `{secG_un Σ}.

  (* unary semantic interpretations *)
  Definition is_dep_ref_un Δ ρ : val -d> iPropO Σ := λ v,
    (<pers> (∃ l1, ⌜v = LocV l1⌝ ∗
      (∀ (E : coPset), ⌜↑Ndep ⊆ E⌝ →
         |={E, E∖↑Ndep}=> ▷ (∃ (b : bool) d1, l1 ↦ (b, d1) ∗ ⌊ TNat ⌋ Δ ρ d1 ∗
                                    (l1 ↦ (b, d1) ={E∖↑Ndep, E}=∗ True)))))%I.

  Definition is_make_dep_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ make_dep_typ ⌋ Δ ρ v)%I.

  Definition is_get_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ get_typ ⌋ₛ (is_dep_ref_un Δ ρ :: Δ) ρ v)%I.

  Definition is_setL_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ setL_typ ⌋ₛ (is_dep_ref_un Δ ρ :: Δ) ρ v)%I.

  Definition is_setH_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ setH_typ ⌋ₛ (is_dep_ref_un Δ ρ :: Δ) ρ v)%I.

  Lemma make_dep_is_make_dep_un Δ ρ :
      ⊢ is_make_dep_un Δ ρ make_dep.
  Proof.
    rewrite /is_make_dep_un /make_dep_typ interp_un_arrow_def.
    iIntros "!>" (?) "? %". by [].
  Qed.

  Lemma get_is_get_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_get_un Δ ρ get.
  Proof.
    intros Henv. rewrite /is_get_un /get_typ. uarrows.
    iIntros "!>" (?) "#Href %Hflow". utvars. cbn.
    iDestruct "Href" as (l1) "[-> Href]".
    iApply ic_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    iApply (ic_step_fupd_bind _ (fill [LetInCtx _])).
    iApply (ic_atomic (icd_step_fupd _) _ StronglyAtomic).
    iMod ("Href" with "[]") as "Hl"; first solve_ndisj.
    iModIntro. iDestruct "Hl" as (b d1) "(Hl1 & #Hd1 & Hclose)".
    iApply ic_step_fupd_load; [done|].
    iFrame. iIntros "!> Hl1 /=".
    iMod ("Hclose" with "Hl1") as "_".
    iModIntro. iApply ic_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    iApply (ic_step_fupd_bind _ (fill [IfCtx _ _])).
    rewrite bool_to_val pair_to_val.
    iApply ic_step_fupd_pure_step; [done|]. iModIntro.
    iApply ic_value; umods. iModIntro.
    destruct b.
    - iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply (ic_step_fupd_bind _ (fill [InjLCtx])).
      iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply ic_value; umods. iModIntro.
      iApply (ic_value (icd_step_fupd _)); umods. iModIntro.
      rewrite interp_un_sum_def. eauto.
    - iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply (ic_step_fupd_bind _ (fill [InjRCtx])).
      iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply ic_value; umods. iModIntro.
      iApply (ic_value (icd_step_fupd _)); umods. iModIntro.
      rewrite interp_un_sum_def. eauto.
  Qed.

  Lemma setH_is_setH_un Δ ρ :
    ⊢ is_setH_un Δ ρ setH.
  Proof.
    rewrite /is_setH_un /setH_typ. uarrows.
    iIntros "!>" (?) "_ %Hflow". by case Hflow.
  Qed.

  Lemma setL_is_setL_un Δ ρ :
    ⊢ is_setL_un Δ ρ setL.
  Proof.
    rewrite /is_setL_un /setL_typ. uarrows.
    iIntros "!>" (?) "_ %Hflow". by case Hflow.
  Qed.

End un_defs.

Notation is_dep_ref_left := (@is_dep_ref_un _ secG_un_left).
Notation is_dep_ref_right := (@is_dep_ref_un _ secG_un_right).
Notation projl Θ := Θ.*2.*1.
Notation projr Θ := Θ.*2.*2.

Section bi_defs.
  Context `{!secG Σ}.

  (* The internal invariant  *)
  Definition dep_inv Θ ρ l1 l2 :=
    (∃ (b : bool) d1 d2, l1 ↦ₗ (b, d1) ∗ l2 ↦ᵣ (b, d2)
        ∗ ⟦ TNat @ (if b then H else L) ⟧ₛ Θ ρ (d1, d2))%I.

  (* binary semantic interpretations *)
  Definition is_dep_ref Θ ρ : val * val -d> iPropO Σ := λ vv,
    (∃ l1 l2, ⌜vv.1 = LocV l1⌝ ∗ ⌜vv.2 = LocV l2⌝ ∗ inv Ndep (dep_inv Θ ρ l1 l2))%I.

  Definition is_get Θ ρ (vv : val * val) :=
    (⟦ get_typ ⟧ₛ ((is_dep_ref Θ ρ,
                   (is_dep_ref_left (projl Θ) ρ,
                    is_dep_ref_right (projr Θ) ρ)) :: Θ) ρ vv)%I.

  Definition is_setL Θ ρ (vv : val * val) :=
    (⟦ setL_typ ⟧ₛ ((is_dep_ref Θ ρ,
                   (is_dep_ref_left (projl Θ) ρ,
                    is_dep_ref_right (projr Θ) ρ)) :: Θ) ρ vv)%I.

  Definition is_setH Θ ρ (vv : val * val) :=
    (⟦ setH_typ ⟧ₛ ((is_dep_ref Θ ρ,
                   (is_dep_ref_left (projl Θ) ρ,
                    is_dep_ref_right (projr Θ) ρ)) :: Θ) ρ vv)%I.

  Definition is_dep Θ ρ : val * val -d> iPropO Σ := λ vv,
    (∃ ll getp setLp setHp, ⌜vv.1 = (ll.1, getp.1, setLp.1, setHp.1)%V⌝ ∗
                            ⌜vv.2 = (ll.2, getp.2, setLp.2, setHp.2)%V⌝ ∗
         is_dep_ref Θ ρ ll ∗ is_get Θ ρ getp ∗ is_setL Θ ρ setLp ∗ is_setH Θ ρ setHp)%I.

  Definition is_make_dep Θ ρ (vv : val * val) :=
    (⟦ make_dep_typ ⟧ Θ ρ vv)%I.

  (* functions satisfy their binary interpretations *)
  Lemma get_is_get Θ ρ :
    envs_Persistent Θ →
    ⊢ is_get Θ ρ (get, get).
  Proof.
    intros Henv. rewrite /is_get /get_typ. uarrows.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    iSplit; iApply get_is_get_un.
    iIntros "!>" ([w1 w2]) "Href".
    rewrite /is_dep_ref /=. utvars.
    rewrite bool_decide_eq_true_2 //=.
    iDestruct "Href" as (l1 l2) "(-> & -> & Hinv)".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    asimpl.
    iApply (ic_left_strong_bind _ _ (fill [LetInCtx _]) (fill [LetInCtx _])).
    cbn. iModIntro.
    iApply (ic_double_atomic_lr _ _ StronglyAtomic).
    iInv (Ndep) as (b d1 d2) "(Hl1 & Hl2 & #Hd)" "Hclose".
    iModIntro.
    iApply ((@ic_step_fupd_load _ secG_un_left)); [done|].
    iFrame. iIntros "!> Hl1".
    iApply ((@ic_fupd_load _ secG_un_right)); [done|].
    iFrame. iIntros "Hl2".
    iMod ("Hclose" with "[-]") as "_".
    { iNext. iExists _,_,_. by iFrame. }
    iModIntro. cbn. rewrite !bool_to_val !pair_to_val.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    asimpl. iModIntro.
    iApply (ic_left_strong_bind _ _ (fill [IfCtx _ _]) (fill [IfCtx _ _])).
    rewrite !bool_to_val.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply ic_value; umods. rewrite bool_to_val. iModIntro.
    iApply (ic_value (icd_right _)); umods.
    iModIntro. destruct b.
    - iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      iModIntro. rewrite !bool_to_val !pair_to_val.
      iApply (ic_left_strong_bind _ _ (fill [InjLCtx]) (fill [InjLCtx])).
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      rewrite -/of_val /=. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def bool_decide_eq_true_2 //.
      rewrite interp_sum_def; eauto.
    - iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      iModIntro. rewrite !bool_to_val !pair_to_val.
      iApply (ic_left_strong_bind _ _ (fill [InjRCtx]) (fill [InjRCtx])).
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      rewrite -/of_val /=. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def bool_decide_eq_true_2 //.
      rewrite interp_sum_def; eauto.
  Qed.

  Lemma setL_is_setL Θ ρ :
    envs_Persistent Θ →
    ⊢ is_setL Θ ρ (setL, setL).
  Proof.
    intros Henv. rewrite /is_setL /setL_typ. uarrows.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply setL_is_setL_un. }
    iIntros "!>" ([w1 w2]) "Href /=".
    rewrite interp_sec_def bool_decide_eq_true_2 //.
    rewrite interp_prod_def /=.
    iDestruct "Href" as (d1 b1 d2 b2) "(-> & -> & Href & Hd)".
    rewrite {1}interp_sec_def bool_decide_eq_true_2 // interp_tvar_def /=.
    rewrite {1}/is_dep_ref /=.
    iDestruct "Href" as (l1 l2) "(-> & -> & Hinv)".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro. asimpl.
    iApply (ic_left_strong_bind _ _ (fill [StoreLCtx _]) (fill [StoreLCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro. rewrite !bool_to_val !loc_to_val.
    iApply (ic_left_strong_bind _ _ (fill [PairRCtx _; StoreRCtx _]) (fill [PairRCtx _; StoreRCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro.
    iApply (ic_double_atomic_lr _ _ StronglyAtomic).
    iInv (Ndep) as (b d1 d2) "(Hl1 & Hl2 & _)" "Hclose".
    iModIntro. rewrite !loc_to_val !bool_to_val !pair_to_val.
    iApply ((@ic_step_fupd_store _ secG_un_left)); [done|].
    iFrame. iIntros "!> Hl1".
    iApply ((@ic_fupd_store _ secG_un_right)); [done|].
    iFrame. iIntros "Hl2".
    iMod ("Hclose" with "[-]") as "_".
    { iNext. iExists _,_,_. iFrame. unats.
      rewrite bool_decide_eq_true_2 //. }
    uunits. rewrite bool_decide_eq_true_2 //.
  Qed.

  (* the proof is very similar to setL above *)
  Lemma setH_is_setH Θ ρ :
    envs_Persistent Θ →
    ⊢ is_setH Θ ρ (setH, setH).
  Proof.
    intros Henv. rewrite /is_setH /setH_typ. uarrows.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply setH_is_setH_un. }
    iIntros "!>" ([w1 w2]) "Href /=".
    rewrite interp_sec_def bool_decide_eq_true_2 //.
    rewrite interp_prod_def /=.
    iDestruct "Href" as (d1 b1 d2 b2) "(-> & -> & Href & Hd)".
    rewrite !interp_sec_def bool_decide_eq_true_2 //
            bool_decide_eq_false_2 // interp_tvar_def /=.
    rewrite {1}/is_dep_ref /=.
    iDestruct "Href" as (l1 l2) "(-> & -> & Hinv)".
    iDestruct "Hd" as "[Hd1 Hd2]".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro. asimpl.
    iApply (ic_left_strong_bind _ _ (fill [StoreLCtx _]) (fill [StoreLCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro. rewrite !bool_to_val !loc_to_val.
    iApply (ic_left_strong_bind _ _ (fill [PairRCtx _; StoreRCtx _]) (fill [PairRCtx _; StoreRCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro.
    iApply (ic_double_atomic_lr _ _ StronglyAtomic).
    iInv (Ndep) as (b d1 d2) "(Hl1 & Hl2 & _)" "Hclose".
    iModIntro. rewrite !loc_to_val !bool_to_val !pair_to_val.
    iApply ((@ic_step_fupd_store _ secG_un_left)); [done|].
    iFrame. iIntros "!> Hl1".
    iApply ((@ic_fupd_store _ secG_un_right)); [done|].
    iFrame. iIntros "Hl2".
    iMod ("Hclose" with "[-]") as "_".
    { iNext. iExists _,_,_. iFrame. unats. rewrite bool_decide_eq_false_2 //.
      iDestruct "Hd1" as (?) "->". iDestruct "Hd2" as (?) "->". eauto. }
    uunits. rewrite bool_decide_eq_true_2 //.
  Qed.

  Lemma is_dep_ref_coh Θ ρ :
    envs_Persistent Θ → env_coherent Θ ⊢
    <pers> (∀ vv : val * val, is_dep_ref Θ ρ vv →
              (is_dep_ref_left (projl Θ) ρ vv.1) ∧ (is_dep_ref_right (projr Θ) ρ vv.2)).
  Proof.
    intros Henv. iIntros "#Hcoh !>" ([v1 v2]) "Hdep /=".
    rewrite /is_dep_ref /is_dep_ref_un /=.
    iDestruct "Hdep" as (l1' l2') "(-> & -> & #Hdep)". iSplit; iModIntro.
    - iExists _. iSplit; [done|].
      iIntros (E HE).
      iInv (Ndep) as (b d1 d2) "(Hl1 & Hl2 & #Hd)" "Hclose".
      do 2 iModIntro. iExists b, d1. iFrame.
      iDestruct (secbin_subsumes_secun with "[$Hd]") as "[Hd1 _]"; [done|].
      rewrite interp_un_sec_def. iFrame "#". iIntros "Hl1".
      iMod ("Hclose" with "[-]") as "_"; [|done]. iNext.
      iExists _,_,_. by iFrame.
    - iExists _. iSplit; [done|].
      iIntros (E HE).
      iInv (Ndep) as (b d1 d2) "(Hl1 & Hl2 & #Hd)" "Hclose".
      do 2 iModIntro. iExists b, d2. iFrame.
      iDestruct (secbin_subsumes_secun with "[$Hd]") as "[_ Hd1]"; [done|].
      rewrite interp_un_sec_def. iFrame "#". iIntros "Hl2".
      iMod ("Hclose" with "[-]") as "_"; [|done]. iNext.
      iExists _,_,_. by iFrame.
  Qed.

  Lemma make_dep_is_make_dep Θ ρ :
    envs_Persistent Θ →
    env_coherent Θ ⊢ is_make_dep Θ ρ (make_dep, make_dep).
  Proof.
    iIntros (Henv) "#Hcoh".
    rewrite /is_make_dep /make_dep_typ. uarrows.
    iSplit; last first.
    { iSplit; iApply make_dep_is_make_dep_un. }
    iIntros "!>" ([w1 w2]) "#Hn".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro.
    iApply (ic_left_strong_bind _ _(fill [PairLCtx _; PairLCtx _; PairLCtx _; PackCtx])
                                   (fill [PairLCtx _; PairLCtx _; PairLCtx _; PackCtx])); cbn.
    rewrite !bool_to_val !pair_to_val.
    iApply ic_un_bi_lr.
    iApply ((@ic_step_fupd_alloc _ secG_un_left)); [done|].
    iIntros "!>" (l1) "Hl1".
    iApply ((@ic_step_fupd_alloc _ secG_un_right)); [done|].
    iIntros "!>" (l2) "Hl2". cbn.
    rewrite !loc_to_val !lam_to_val -/get -/setL -/setH !pair_to_val.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    iMod (inv_alloc Ndep _ (dep_inv _ _ l1 l2) with "[Hl1 Hl2]") as "#Hinv".
    { iNext. iExists _,_,_. iFrame. iFrame "#". }
    iModIntro. rewrite !interp_sec_def.
    rewrite {1}bool_decide_eq_false_2 // {1}bool_decide_eq_true_2 //.
    rewrite /dep_typ interp_exist_def.
    iModIntro. iExists (is_dep_ref _ _),
                 (is_dep_ref_left _ _), (is_dep_ref_right _ _).
    rewrite -/get -/setL -/setH.
    repeat (iSplit; [iPureIntro; apply _|]).
    iSplit; [by iApply is_dep_ref_coh|].
    iExists (_, _). cbn. do 2 (iSplit; [done|]).
    rewrite interp_sec_def bool_decide_eq_true_2 // interp_prod_def.
    iExists (_,_)%V,_,(_,_)%V,_. do 2 (iSplit; [done|]).
    iSplit; [|iApply setH_is_setH].
    rewrite interp_sec_def bool_decide_eq_true_2 // interp_prod_def.
    iExists (_,_)%V, _, (_,_)%V, _. do 2 (iSplit; [done|]).
    iSplit; [|iApply setL_is_setL].
    rewrite interp_sec_def bool_decide_eq_true_2 // interp_prod_def.
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    rewrite interp_sec_def bool_decide_eq_true_2 // interp_tvar_def /=.
    iSplit; [iExists _,_; eauto|].
    iApply get_is_get.
  Qed.

  Lemma client_composed_related :
    [] ⊨ client (# make_dep) ≤ₗ client (# make_dep) : (client_type_inner @ L).
  Proof.
    iIntros (Θ ρ vvs Hpers) "[#Hcoh _]".
    iDestruct (binary_fundamental _ _ _ _ client_typed with "[$Hcoh]") as "Hclient".
    { iApply (interp_env_nil _ ρ). }
    asimpl.
    iApply (ic_left_strong_bind _ _ (fill [AppLCtx _]) (fill [AppLCtx _])).
    iApply (ic_wand_r ic_binary). iSplitL.
    { iApply "Hclient". }
    iClear "Hclient".
    iIntros (???) "#HclientV /=".
    rewrite /client_type interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "HclientV" as "[#HclientV _]".
    rewrite !lam_to_val.
    iApply ("HclientV" $! (_,_)).
    rewrite interp_sec_def bool_decide_eq_true_2 //.
    iApply ((make_dep_is_make_dep _ ρ) with "[$]").
  Qed.

End bi_defs.
