From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This example is adapted from [Fennel & Thiemann, CSF 2013]

     https://ieeexplore.ieee.org/document/6595831
 *)

(* λ isPrivileged worker report,
       if isPrivileged
         then report <- report + !infoH
         else ();
       worker report
 *)
Definition addPrivileged : val :=
  λ: λ: λ:
    (if: $2 then $0 <- !$0 + !$3 else ()%V);;
  $1 $0.

Definition Report : type := TNat.

(* (ref Reportᴴ)ᴸ →ᴴ ()ᴸ *)
Definition TsendToManager : type :=
  ((ref (Report @ H) @ L) →[H] (() @ L))%type.
(* (ref Reportᴸ)ᴸ →ᴴ ()ᴸ *)
Definition TsendToFacebook : type :=
  ((ref (Report @ L) @ L) →[L] (() @ L))%type.

(* We can typecheck [addPrivileged] with a "high" worker *)
(* Boolᴸ →ᴴ TsendToManagerᴸ →ᴴ ref Reportᴴ →ᴴ () *)
Definition addPrivileged_type : type :=
  TBool @ L →[H] (((TsendToManager @ L) →[H]
    (((ref (Report @ H) @ L) →[H] (() @ L)) @ L)) @ L).

Lemma addPrivileged_typed :
  [ref (Report @ H) @ L] # L ⊢ₜ #addPrivileged : addPrivileged_type @ L.
Proof.
  do 3 constructor. econstructor.
  - econstructor; try by constructor.
    econstructor; try by constructor.
    do 2 econstructor; try by constructor.
    + by (do 2 econstructor).
    + by (do 2 econstructor).
  - econstructor; try by constructor.
Qed.

(* We can also typecheck an application to a "high" worker *)
Definition sendToManager : val :=
  λ: ()%V.
Lemma sendToManager_typed :
  [ref (Report @ H) @ L] # L ⊢ₜ #sendToManager : TsendToManager @ L.
Proof. do 2 constructor. Qed.

Lemma addPrivileged_sendToManager_typed :
  [ref (Report @ H) @ L] # L
   ⊢ₜ (#addPrivileged) (#true) (#sendToManager) :
        ((ref (Report @ H) @ L) →[H] (() @ L)) @ L.
Proof.
  econstructor.
  - econstructor.
    + eapply addPrivileged_typed.
    + constructor.
    + constructor.
    + do 2 constructor.
  - apply sendToManager_typed.
  - constructor.
  - do 2 constructor.
Qed.

(* But we cannot typecheck [addPrivileged] with a "low" worker as the type
   system does not track the correspondence between the security level of the
   worker and the isPrivileged flag *)
Definition addPrivileged_type_wrong : type :=
  TBool @ L →[H] (((TsendToFacebook @ L) →[H]
      (((ref (Report @ L) @ L) →[H] (() @ L)) @ L)) @ L).

Lemma addPrivileged_typed_wrong :
  [ref (Report @ H) @ L] # L ⊢ₜ #addPrivileged : addPrivileged_type_wrong @ L.
Proof.
  do 3 constructor. econstructor.
  - econstructor; try by constructor.
    econstructor; try by constructor.
    + do 2 econstructor; try by constructor.
      * by (do 2 econstructor).
      * econstructor; try by constructor.
        rewrite /Report.
        (* STUCK *)
        Abort.

Definition sendToFacebook : val :=
  λ: ()%V.
Lemma sendToFacebook_typed :
  [ref (Report @ H) @ L] # L ⊢ₜ #sendToFacebook : TsendToFacebook @ L.
Proof. do 2 constructor. Qed.

(* However, semantically, applying the "low" worker to [addPrivileged] is secure
   as we can prove! *)
Section bi_defs.
  Context `{!secG Σ}.

  Lemma addPrivileged_sendToFacebook_semtyped :
    [] ⊨ (#addPrivileged) (#false) (#sendToFacebook) ≤ₗ
         (#addPrivileged) (#false) (#sendToFacebook)
       : ((ref (Report @ L) @ L) →[H] (() @ L)) @ L.
  Proof.
    iIntros (Θ ρ vvs Hpers) "[#Hcoh _]".
    asimpl. rewrite !lam_to_val !bool_to_val.
    iApply (mwp_left_strong_bind _ _ (fill [AppLCtx _])
                                    (fill [AppLCtx _])); cbn.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    asimpl. rewrite !lam_to_val. iModIntro.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwpd_right _)); umods. iModIntro.
    iApply mwp_left_pure_step; [done|].
    iApply mwp_left_pure_step_index; [done|].
    iModIntro. asimpl.
    iApply (mwp_value mwp_binary); umods.
    iApply (mwp_value (mwpd_right _)); umods. iModIntro.
    rewrite [⟦ (_ →[H] _ @ _) @ _ ⟧ₛ _ _ _]interp_sec_def interp_arrow_def.
    rewrite bool_decide_eq_true_2 //.
    repeat iSplit.
    - iIntros "!>" (?) "_ /=".
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iModIntro. asimpl.
      iApply (mwp_left_strong_bind _ _ (fill [SeqCtx _])
                                  (fill [SeqCtx _])); cbn.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_value mwp_binary); umods.
      iApply (mwp_value (mwpd_right _)); umods. do 2 iModIntro.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|]. iModIntro.
      iApply mwp_left_pure_step; [done|].
      iApply mwp_left_pure_step_index; [done|].
      iApply (mwp_value mwp_binary); umods.
      iApply (mwp_value (mwpd_right _)); umods. do 2 iModIntro.
      rewrite interp_sec_def interp_unit_def.
      rewrite bool_decide_eq_true_2 //.
    - rewrite interp_un_arrow_def.
      iIntros "!>" (?) "_ /= %".
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      iApply (mwp_step_fupd_bind _ (fill [SeqCtx _])).
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      asimpl.
      iApply (mwp_value (mwpd_step_fupd _)); umods. iModIntro.
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      asimpl.
      iApply (mwp_value (mwpd_step_fupd _)); umods. iModIntro.
      rewrite interp_un_sec_def interp_un_unit_def //.
    - rewrite interp_un_arrow_def.
      iIntros "!>" (?) "_ /= %".
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      iApply (mwp_step_fupd_bind _ (fill [SeqCtx _])).
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      asimpl.
      iApply (mwp_value (mwpd_step_fupd _)); umods. iModIntro.
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      iApply mwp_step_fupd_pure_step; [done|]. iModIntro.
      asimpl.
      iApply (mwp_value (mwpd_step_fupd _)); umods. iModIntro.
      rewrite interp_un_sec_def interp_un_unit_def //.
  Qed.

End bi_defs.
