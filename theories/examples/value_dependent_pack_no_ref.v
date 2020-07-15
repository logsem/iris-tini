From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This is example is a variation of [value_dependent_pack.v] that do not use
   references but exploits data hiding to provide the same kind of
   functionality. Notice here that we can have multiple copies of alpha that do
   not have to agree.  *)
Definition get : val :=
  λ: if: Proj1 $0 then InjL (Proj2 $0) else InjR (Proj2 $0).
Definition setL : val :=
  λ: (#false, (Proj2 $0)).
Definition setH : val :=
  λ: (#true, (Proj2 $0)).
Definition make_dep : expr :=
  pack: ((#true, $0), (# get), (# setL), (# setH)).

(* (αᴸ →ᴴ (Natᴴ + Natᴸ)ᴸ)ᴸ *)
Definition get_typ : sectype :=
  (($0 @ L) →[H] (((TNat @ H) + (TNat @ L)) @ L)) @ L.

(* ((αᴸ × Natᴸ)ᴸ →ᴴ αᴸ)ᴸ *)
Definition setL_typ : sectype :=
  ((($0 @ L) * (TNat @ L)) @ L →[H] ($0 @ L)) @ L.

(* ((αᴸ × Natᴴ)ᴸ →ᴴ αᴸ)ᴸ *)
Definition setH_typ : sectype :=
  ((($0 @ L) * (TNat @ H)) @ L →[H] ($0 @ L)) @ L.

(* ∃ α,
     (αᴸ *
     (αᴸ →ᴴ (Natᴸ + Natᴸ)ᴸ)ᴸ *
    ((αᴸ × Natᴸ)ᴸ →ᴴ αᴸ)ᴸ *
    ((αᴸ × Natᴴ)ᴸ →ᴴ αᴸ)ᴸ)ᴸ
 *)
Definition make_dep_typ : type :=
  ∃: ((((((($0 @ L) * get_typ) @ L) * setL_typ) @ L) * setH_typ) @ L).

(************************ Proofs ************************)
Definition Ndep : namespace := nroot.@"dep".

Section un_defs.
  Context `{secG_un Σ}.

  (* unary semantic interpretations *)
  Definition is_dep_pair_un  : val -d> iPropO Σ := λ v,
    (∃ (b : bool) d, ⌜v = (b, d)%V⌝ ∗ ⌊ TNat ⌋ [] [] d)%I.

  Definition is_get_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ get_typ ⌋ₛ (is_dep_pair_un :: Δ) ρ v)%I.

  Definition is_setL_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ setL_typ ⌋ₛ (is_dep_pair_un :: Δ) ρ v)%I.

  Definition is_setH_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ setH_typ ⌋ₛ (is_dep_pair_un :: Δ) ρ v)%I.

  Lemma get_is_get_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_get_un Δ ρ get.
  Proof.
    rewrite /is_get_un /get_typ interp_un_sec_def interp_un_arrow_def /get.
    iIntros (Hpers) "!> %v #Hpair %Hflow". utvars.
    iDestruct "Hpair" as (b d) "[-> Hpair]".
    iApply ic_step_fupd_pure_step; [done|].
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
      rewrite interp_un_sum_def; auto.
    - iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply (ic_step_fupd_bind _ (fill [InjRCtx])).
      iApply ic_step_fupd_pure_step; [done|]. iModIntro.
      iApply ic_value; umods. iModIntro.
      iApply (ic_value (icd_step_fupd _)); umods. iModIntro.
      rewrite interp_un_sum_def; auto.
  Qed.

  Lemma setH_is_setH_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_setH_un Δ ρ setH.
  Proof.
    rewrite /is_setH_un /setH_typ interp_un_sec_def interp_un_arrow_def /setH.
    iIntros (Hpers) "!> % Hpair _". cbn.
    rewrite interp_un_sec_def interp_un_prod_def.
    iDestruct "Hpair" as (p v) "(-> & _ & Hv)".
    iApply ic_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    rewrite bool_to_val.
    iApply (ic_step_fupd_bind _ (fill [PairRCtx _])).
    iApply ic_step_fupd_pure_step; [done|]. iModIntro.
    iApply ic_value; umods. iModIntro.
    rewrite bool_to_val pair_to_val.
    iApply (ic_value (icd_step_fupd _)); umods.
    iModIntro.
    rewrite interp_un_sec_def interp_un_tvar_def /is_dep_pair_un /=.
    eauto.
  Qed.


  Lemma setL_is_setL_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_setL_un Δ ρ setL.
  Proof.
    rewrite /is_setL_un /setL_typ interp_un_sec_def interp_un_arrow_def /setL.
    iIntros (Hpers) "!> % Hpair _". cbn.
    rewrite interp_un_sec_def interp_un_prod_def.
    iDestruct "Hpair" as (p v) "(-> & _ & Hv)".
    iApply ic_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    rewrite bool_to_val.
    iApply (ic_step_fupd_bind _ (fill [PairRCtx _])).
    iApply ic_step_fupd_pure_step; [done|]. iModIntro.
    iApply ic_value; umods. iModIntro.
    rewrite bool_to_val pair_to_val.
    iApply (ic_value (icd_step_fupd _)); umods.
    iModIntro.
    rewrite interp_un_sec_def interp_un_tvar_def /is_dep_pair_un /=.
    eauto.
  Qed.

End un_defs.

Notation is_dep_pair_left := (@is_dep_pair_un _ secG_un_left).
Notation is_dep_pair_right := (@is_dep_pair_un _ secG_un_right).

Section bi_defs.
  Context `{!secG Σ}.

  (* binary semantic interpretations *)
  Definition is_dep_pair : val * val -d> iPropO Σ := λ vv,
    (∃ (b : bool) d1 d2, ⌜vv.1 = (b, d1)%V⌝ ∗ ⌜vv.2 = (b, d2)%V⌝
        ∗ ⟦ TNat @ (if b then H else L) ⟧ₛ [] [] (d1, d2))%I.

  Definition is_get Θ ρ (vv : val * val) :=
    (⟦ get_typ ⟧ₛ ((is_dep_pair, (is_dep_pair_left, is_dep_pair_right)) :: Θ) ρ vv)%I.

  Definition is_setL Θ ρ (vv : val * val) :=
    (⟦ setL_typ ⟧ₛ ((is_dep_pair, (is_dep_pair_left, is_dep_pair_right)) :: Θ) ρ vv)%I.

  Definition is_setH Θ ρ (vv : val * val) :=
    (⟦ setH_typ ⟧ₛ ((is_dep_pair, (is_dep_pair_left, is_dep_pair_right)) :: Θ) ρ vv)%I.

  Definition is_dep Θ ρ : val * val -d> iPropO Σ := λ vv,
    (∃ ll getp setLp setHp, ⌜vv.1 = (ll.1, getp.1, setLp.1, setHp.1)%V⌝ ∗
                            ⌜vv.2 = (ll.2, getp.2, setLp.2, setHp.2)%V⌝ ∗
         is_dep_pair ll ∗ is_get Θ ρ getp ∗ is_setL Θ ρ setLp ∗ is_setH Θ ρ setHp)%I.

  (* functions satisfy their binary interpretations *)
  Lemma get_is_get Θ ρ :
    envs_Persistent Θ →
    ⊢ is_get Θ ρ (get, get).
  Proof.
    intros ?. rewrite /is_get /get_typ interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply get_is_get_un. }
    iIntros "!>" ([w1 w2]) "Hpair".
    rewrite interp_sec_def interp_tvar_def /is_dep_pair /=.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hpair" as (b d1 d2) "(-> & -> & Hinv)".
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
      cbn.
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def interp_sum_def.
      rewrite bool_decide_eq_true_2 //; auto.
    - iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      iModIntro. rewrite !bool_to_val !pair_to_val.
      iApply (ic_left_strong_bind _ _ (fill [InjRCtx]) (fill [InjRCtx])).
      cbn.
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|].
      iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def interp_sum_def.
      rewrite bool_decide_eq_true_2 //; auto.
  Qed.

  Lemma setL_is_setL Θ ρ :
    envs_Persistent Θ →
    ⊢ is_setL Θ ρ (setL, setL).
  Proof.
    intros ?. rewrite /is_setL /setL_typ interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply setL_is_setL_un. }
    iIntros "!>" ([w1 w2]) "Hdep /=". rewrite interp_sec_def interp_prod_def.
    rewrite bool_decide_eq_true_2 //=.
    iDestruct "Hdep" as (p1 v1 p2 v2) "(-> & -> & Hpair & Hd)".
    rewrite /is_dep_pair interp_sec_def interp_tvar_def /=.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hpair" as (b d1 d2) "(-> & -> & _)".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro. asimpl. rewrite !bool_to_val.
    iApply (ic_left_strong_bind _ _ (fill [PairRCtx _]) (fill [PairRCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro. rewrite !bool_to_val !pair_to_val.
    iApply (ic_value ic_binary); umods.
    rewrite !bool_to_val !pair_to_val.
    iApply (ic_value (icd_right _)); umods.
    iModIntro. rewrite [⟦ $0 @ L ⟧ₛ _ _ _]interp_sec_def interp_tvar_def.
    rewrite bool_decide_eq_true_2 //.
    iExists _,_,_. eauto.
   Qed.

  (* the proof is symmetric to the one for setL above *)
  Lemma setH_is_setH Θ ρ :
    envs_Persistent Θ →
    ⊢ is_setH Θ ρ (setH, setH).
  Proof.
    intros ?. rewrite /is_setH /setH_typ interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply setH_is_setH_un. }
    iIntros "!>" ([w1 w2]) "Hdep /=". rewrite interp_sec_def interp_prod_def.
    rewrite bool_decide_eq_true_2 //=.
    iDestruct "Hdep" as (p1 v1 p2 v2) "(-> & -> & Hpair & Hd)".
    rewrite /is_dep_pair interp_sec_def interp_tvar_def /=.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hpair" as (b d1 d2) "(-> & -> & _)".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iModIntro. asimpl. rewrite !bool_to_val.
    iApply (ic_left_strong_bind _ _ (fill [PairRCtx _]) (fill [PairRCtx _])).
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods.
    do 2 iModIntro. rewrite !bool_to_val !pair_to_val.
    iApply (ic_value ic_binary); umods.
    rewrite !bool_to_val !pair_to_val.
    iApply (ic_value (icd_right _)); umods.
    iModIntro. rewrite [⟦ $0 @ L ⟧ₛ _ _ _]interp_sec_def interp_tvar_def.
    rewrite bool_decide_eq_true_2 //.
    iExists _,_,_. eauto.
   Qed.

  Lemma is_dep_pair_coh :
    ⊢ <pers> (∀ vv : val * val, is_dep_pair vv → (is_dep_pair_left vv.1) ∧ (is_dep_pair_right vv.2)).
  Proof.
    iIntros "!>" ([v1 v2]) "Hdep /=".
    rewrite /is_dep_pair /is_dep_pair_un /=.
    iDestruct "Hdep" as (b d1 d2) "(-> & -> & Hdep)". iSplit; destruct b.
    - iExists true, _. iSplit; [done|].
      rewrite interp_sec_def bool_decide_eq_false_2 //.
      by iDestruct "Hdep" as "[? ?]".
    - iExists false, _. iSplit; [done|].
      iDestruct (secbin_subsumes_secun with "[$Hdep]") as "[??]".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def //.
    - iExists true, _. iSplit; [done|].
      iDestruct (secbin_subsumes_secun with "[$Hdep]") as "[??]".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def //.
    - iExists false, _. iSplit; [done|].
      iDestruct (secbin_subsumes_secun with "[$Hdep]") as "[??]".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def //.
  Qed.

  Lemma make_dep_spec :
    [TNat @ H] ⊨ make_dep ≤ₗ make_dep : make_dep_typ @ L.
  Proof.
    iIntros (Θ ρ vvs Hpers) "[#Hcoh #Henv]".
    iDestruct (interp_env_length with "Henv") as %Hlen.
    destruct vvs as [| []]; [done|]; clear Hlen.
    iDestruct (interp_env_cons with "Henv") as "[#Hn _]". asimpl.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hn]") as "[? ?]".
    rewrite [⟦ make_dep_typ @ _ ⟧ₛ _ _ _]interp_sec_def.
    rewrite {1}bool_decide_eq_true_2 // /make_dep_typ.
    rewrite interp_exist_def.
    do 2 iModIntro.
    iExists is_dep_pair, is_dep_pair_left, is_dep_pair_right.
    rewrite -/get -/setL -/setH.
    repeat (iSplit; [iPureIntro; apply _|]).
    iSplit; [iApply is_dep_pair_coh|].
    iExists (_, _). cbn. do 2 (iSplit; [done|]).
    rewrite [⟦ _ * _ @ L ⟧ₛ _ _ _]interp_sec_def !interp_prod_def.
    rewrite bool_decide_eq_true_2 //.
    iExists (_,_)%V,_,(_,_)%V,_. do 2 (iSplit; [done|]).
    iSplit; [|iApply setH_is_setH].
    rewrite [⟦ _ * _ @ L ⟧ₛ _ _ _]interp_sec_def !interp_prod_def.
    rewrite bool_decide_eq_true_2 //.
    iExists (_,_)%V, _, (_,_)%V, _. do 2 (iSplit; [done|]).
    iSplit; [|iApply setL_is_setL].
    rewrite [⟦ _ * _ @ L ⟧ₛ _ _ _]interp_sec_def !interp_prod_def.
    rewrite bool_decide_eq_true_2 //.
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    iSplit.
    { rewrite /is_dep_pair.
      rewrite [⟦ $0 @ L ⟧ₛ _ _ _]interp_sec_def interp_tvar_def.
      rewrite bool_decide_eq_true_2 //. iExists _,_,_. eauto. }
    iApply get_is_get.
  Qed.

End bi_defs.
