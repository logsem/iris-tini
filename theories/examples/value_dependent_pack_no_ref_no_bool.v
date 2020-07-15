From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This example is inspired by [value_dependent_pack_no_ref.v] but instead of a
   boolean to determine the sensitivity level we use a predicate (n < 42) on a
   value to determine the sensitivity level. *)
Definition get : val :=
  λ: if: (Proj1 $0) < 42 then InjL (Proj2 $0) else InjR (Proj2 $0).

Definition make_dep : expr :=
  λ: pack: ($0, (# get)).

(* (αᴸ →ᴴ (Natᴴ + Natᴸ)ᴸ)ᴸ *)
Definition get_typ : sectype :=
  (($0 @ L) →[H] (((TNat @ H) + (TNat @ L)) @ L)) @ L.

(* ∃ α,
     (αᴸ ×
     (αᴸ →ᴴ (NatH + Natᴸ)ᴸ)ᴸ)ᴸ
 *)
Definition make_dep_typ : type :=
  ∃: ((($0 @ L) * get_typ) @ L).

(************************ Proofs ************************)

Section un_defs.
  Context `{secG_un Σ}.

  (* unary semantic interpretations *)
  Definition is_dep_pair_un  : val -d> iPropO Σ := λ v,
    (∃ n d, ⌜v = (n, d)%V⌝ ∗ ⌊ TNat ⌋ [] [] n ∗ ⌊ TNat ⌋ [] [] d)%I.

  Definition is_get_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ get_typ ⌋ₛ (is_dep_pair_un :: Δ) ρ v)%I.

  Lemma get_is_get_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_get_un Δ ρ get.
  Proof.
    rewrite /is_get_un /get_typ interp_un_sec_def interp_un_arrow_def /get.
    iIntros (Hpers) "!> %v #Hpair %Hflow". utvars.
    iDestruct "Hpair" as (b d) "[-> [Hn Hd]]". unats.
    iDestruct "Hn" as (n) "->".
    iApply ic_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    iApply (ic_step_fupd_bind _ (fill [BinOpLCtx _ _; IfCtx _ _])).
    rewrite nat_to_val pair_to_val.
    iApply ic_step_fupd_pure_step; [done|]. rewrite -/of_val. iModIntro.
    iApply ic_value; umods. iModIntro.
    iApply (ic_step_fupd_bind _ (fill [IfCtx _ _])).
    iApply ic_step_fupd_pure_step; [done|]. rewrite -/of_val. iModIntro.
    iApply ic_value; umods. iModIntro.
    case_bool_decide.
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

End un_defs.

Notation is_dep_pair_left := (@is_dep_pair_un _ secG_un_left).
Notation is_dep_pair_right := (@is_dep_pair_un _ secG_un_right).

Section bi_defs.
  Context `{!secG Σ}.

  (* binary semantic interpretations *)
  Definition is_dep_pair : val * val -d> iPropO Σ := λ vv,
    (∃ (n : nat) d1 d2, ⌜vv.1 = (n, d1)%V⌝ ∗ ⌜vv.2 = (n, d2)%V⌝
        ∗ ⟦ TNat @ (if bool_decide (n < 42) then H else L) ⟧ₛ [] [] (d1, d2))%I.

  Definition is_get Θ ρ (vv : val * val) :=
    (⟦ get_typ ⟧ₛ ((is_dep_pair, (is_dep_pair_left, is_dep_pair_right)) :: Θ) ρ vv)%I.

  Definition is_dep Θ ρ : val * val -d> iPropO Σ := λ vv,
    (∃ p getp, ⌜vv.1 = (p.1, getp.1)%V⌝ ∗ ⌜vv.2 = (p.2, getp.2)%V⌝ ∗
         is_dep_pair p ∗ is_get Θ ρ getp )%I.

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
    iDestruct "Hpair" as (n d1 d2) "(-> & -> & Hinv)".
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    asimpl. iModIntro.
    iApply (ic_left_strong_bind _ _ (fill [BinOpLCtx _ _; IfCtx _ _]) (fill [BinOpLCtx _ _; IfCtx _ _])).
    rewrite !nat_to_val.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    iApply ic_value; umods.
    iApply (ic_value (icd_right _)); umods. do 2 iModIntro.
    iApply (ic_left_strong_bind _ _ (fill [IfCtx _ _]) (fill [IfCtx _ _])).
    rewrite !nat_to_val.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|]. cbn.
    rewrite !bool_to_val. iModIntro.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value (icd_right _)); umods. iModIntro.
    case_bool_decide.
    - iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|]. cbn. iModIntro.
      iApply (ic_left_strong_bind _ _ (fill [InjLCtx]) (fill [InjLCtx])).
      rewrite !nat_to_val.
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|]. cbn.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. do 2 iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def interp_sum_def.
      rewrite bool_decide_eq_true_2 //. eauto.
    - iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|]. cbn. iModIntro.
      iApply (ic_left_strong_bind _ _ (fill [InjRCtx]) (fill [InjRCtx])).
      rewrite !nat_to_val.
      iApply ic_left_pure_step; [done|].
      iApply ic_left_pure_step_index; [done|]. cbn.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. do 2 iModIntro.
      iApply (ic_value ic_binary); umods.
      iApply (ic_value (icd_right _)); umods. iModIntro.
      rewrite [⟦ _ + _ @ L ⟧ₛ _ _ _]interp_sec_def interp_sum_def.
      rewrite bool_decide_eq_true_2 //. eauto.
   Qed.

  Lemma is_dep_pair_coh :
    ⊢ <pers> (∀ vv : val * val, is_dep_pair vv → (is_dep_pair_left vv.1) ∧ (is_dep_pair_right vv.2)).
  Proof.
    iIntros "!>" ([v1 v2]) "Hdep /=".
    rewrite /is_dep_pair /is_dep_pair_un /=.
    iDestruct "Hdep" as (n d1 d2) "(-> & -> & Hdep)".
    case_bool_decide; cbn.
    - iDestruct (secbin_subsumes_secun with "[$Hdep]") as "[??] /=".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def.
      iSplit.
      + iExists _,_. iSplit; [done|].
        rewrite !interp_un_nat_def; eauto.
      + iExists _,_. iSplit; [done|].
        rewrite !interp_un_nat_def; eauto.
    - iDestruct (secbin_subsumes_secun with "[$Hdep]") as "[??] /=".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def.
      iSplit.
      + iExists _,_. iSplit; [done|].
        rewrite !interp_un_nat_def; eauto.
      + iExists _,_. iSplit; [done|].
        rewrite !interp_un_nat_def; eauto.
  Qed.

  Lemma make_dep_spec (n d1 d2 : nat) :
    (¬ n < 42 → d1 = d2) → (* input should satisfy the security policy *)
    [] ⊨ make_dep (n, d1)%E  ≤ₗ make_dep (n, d2)%E : make_dep_typ @ L.
  Proof.
    iIntros (Hleq Θ ρ vvs Hpers) "[#Hcoh _]".
    rewrite /make_dep_typ.
    rewrite !nat_to_val !pair_to_val.
    iApply ic_left_pure_step; [done|].
    iApply ic_left_pure_step_index; [done|].
    cbn. iModIntro. asimpl.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    rewrite interp_sec_def bool_decide_eq_true_2 //.
    rewrite interp_exist_def.
    do 2 iModIntro.
    iExists is_dep_pair, is_dep_pair_left, is_dep_pair_right.
    rewrite -/get.
    repeat (iSplit; [iPureIntro; apply _|]).
    iSplit; [iApply is_dep_pair_coh|].
    iExists (_, _). cbn. do 2 (iSplit; [done|]).
    rewrite [⟦ _ * _ @ L ⟧ₛ _ _ _]interp_sec_def !interp_prod_def.
    rewrite bool_decide_eq_true_2 //.
    iExists (_,_)%V,_,(_,_)%V,_. do 2 (iSplit; [done|]).
    iSplit; last iApply get_is_get.
    rewrite /is_dep_pair.
    rewrite [⟦ $0 @ L ⟧ₛ _ _ _]interp_sec_def interp_tvar_def.
    rewrite bool_decide_eq_true_2 //=.
    iExists _,_,_.
    do 2 (iSplit; [done|]).
    case_bool_decide as Heq; rewrite  interp_sec_def interp_nat_def.
    - rewrite bool_decide_eq_false_2 //.
      rewrite !interp_un_sec_def !interp_un_nat_def //=. eauto.
    - rewrite bool_decide_eq_true_2 // (Hleq Heq). eauto.
  Qed.

End bi_defs.
