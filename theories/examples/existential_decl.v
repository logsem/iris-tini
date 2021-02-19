From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

Definition declassify : val :=
  λ: $0.
Definition makeSecret : expr :=
  pack: ($0, # declassify).

Definition declassify_typ : sectype :=
  (($0 @ L) →[L] TNat @ L) @ L.

Definition make_secret_typ : type :=
  ∃: ((($0 @ L) * declassify_typ) @ L).

(************************ Proofs ************************)
Definition Ndep : namespace := nroot.@"dep".

Section un_defs.
  Context `{secG_un Σ}.

  Definition is_secret_un  : val -d> iPropO Σ := λ v,
    (∃ (n : nat), ⌜v = n⌝ ∗ ⌊ TNat ⌋ [] [] n)%I.

  Definition is_declassify_un `{secG_un Σ} Δ ρ (v : val) :=
    (⌊ declassify_typ ⌋ₛ (is_secret_un :: Δ) ρ v)%I.

  Lemma declassify_is_declassify_un Δ ρ :
    env_Persistent Δ →
    ⊢ is_declassify_un Δ ρ declassify.
  Proof using Type.
    rewrite /is_declassify_un /declassify_typ interp_un_sec_def interp_un_arrow_def /declassify.
    iIntros (Hpers) "!> %v #Hnat %Hflow". utvars.
    iDestruct "Hnat" as (n) "[-> Hnat]".
    iApply mwp_step_fupd_pure_step; [done|].
    iModIntro. asimpl.
    rewrite nat_to_val.
    iApply (mwp_value (mwpd_step_fupd _)); umods. iModIntro.
    done.
  Qed.

End un_defs.

Notation is_secret_left := (@is_secret_un _ secG_un_left).
Notation is_secret_right := (@is_secret_un _ secG_un_right).

Section bi_defs.
  Context `{!secG Σ}.

  Definition is_secret: val * val -d> iPropO Σ := λ vv,
    (∃ d1 d2, ⌜vv.1 = d1⌝ ∗ ⌜vv.2 = d2%V⌝
        ∗ ⟦ TNat @ L ⟧ₛ [] [] (d1, d2))%I.

  Definition is_declassify Θ ρ (vv : val * val) :=
    (⟦ declassify_typ ⟧ₛ ((is_secret, (is_secret_left, is_secret_right)) :: Θ) ρ vv)%I.


  Definition is_decl_secret Θ ρ : val * val -d> iPropO Σ := λ vv,
    (∃ secretp declassifyp, ⌜vv.1 = (secretp.1, declassifyp.1)%V⌝ ∗
                            ⌜vv.2 = (secretp.2, declassifyp.2)%V⌝ ∗
         is_secret secretp ∗ is_declassify Θ ρ declassifyp)%I.

  Lemma declassify_is_declassify Θ ρ :
    envs_Persistent Θ →
    ⊢ is_declassify Θ ρ (declassify, declassify).
  Proof.
    intros ?. rewrite /is_declassify /declassify_typ interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    iSplit; last first.
    { iSplit; iApply declassify_is_declassify_un. }
    iIntros "!>" ([w1 w2]) "Hsecret".
    rewrite interp_sec_def interp_tvar_def /is_decl_secret.
    rewrite bool_decide_eq_true_2 //.
    iDestruct "Hsecret" as (d1 d2) "(-> & -> & Hinv)". simpl.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    asimpl. iModIntro.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwpd_right _)); umods. iModIntro.
    done.
  Qed.

  Lemma is_secret_coh :
    ⊢ <pers> (∀ vv : val * val, is_secret vv → (is_secret_left vv.1) ∧ (is_secret_right vv.2)).
  Proof.
    iIntros "!>" ([v1 v2]) "Hsecret /=".
    rewrite /is_secret /is_secret_un /=.
    iDestruct "Hsecret" as (d1 d2) "(-> & -> & Hsecret)". iSplit.
    - iDestruct (secbin_subsumes_secun with "[$Hsecret]") as "[#Hleft _]".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def interp_un_nat_def /=.
      iDestruct "Hleft" as (n) "->". iExists _. iSplit; [done|].
      iExists n; done.
    - iDestruct (secbin_subsumes_secun with "[$Hsecret]") as "[_ #Hright]".
      { rewrite /env_coherent //. }
      rewrite interp_un_sec_def interp_un_nat_def /=.
      iDestruct "Hright" as (n) "->". iExists _. iSplit; [done|].
      iExists n; done.
  Qed.

  Lemma make_secret_spec :
    [TNat @ L] ⊨ makeSecret ≤ₗ makeSecret : make_secret_typ @ L.
  Proof.
    iIntros (Θ ρ vvs Hpers) "[#Hcoh #Henv]".
    iDestruct (interp_env_length with "Henv") as %Hlen.
    destruct vvs as [| []]; [done|]; clear Hlen.
    iDestruct (interp_env_cons with "Henv") as "[#Hn _]". asimpl.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value mwp_right); umods.
    iDestruct (secbin_subsumes_secun with "[$Hcoh $Hn]") as "[? ?]".
    rewrite [⟦ make_secret_typ @ _ ⟧ₛ _ _ _]interp_sec_def.
    rewrite {1}bool_decide_eq_true_2 // /make_secret_typ.
    rewrite interp_exist_def.
    do 2 iModIntro.
    iExists is_secret, is_secret_left, is_secret_right.
    repeat (iSplit; [iPureIntro; apply _|]).
    iSplit; [iApply is_secret_coh|].
    iExists (_, _). cbn. do 2 (iSplit; [done|]).
    rewrite [⟦ _ * _ @ L ⟧ₛ _ _ _]interp_sec_def !interp_prod_def.
    rewrite bool_decide_eq_true_2 //.
    iExists _,_,_,_. do 2 (iSplit; [done|]).
    iSplit; [|iApply declassify_is_declassify].
    { rewrite /is_secret.
      rewrite [⟦ $0 @ L ⟧ₛ _ _ _]interp_sec_def interp_tvar_def.
      rewrite bool_decide_eq_true_2 /=. iExists _,_. eauto. done. }
  Qed.

End bi_defs.
