From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From IC.if_convergent.derived Require Import IC_step_fupd.
From IC.if_convergent.derived.ni_logrel Require Import IC_left IC_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Local Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(*

λ f, default.
     let cache = ref (default, f default) in
     let compute = λ v,
       let result = f v in
       cache <- (v, result); result in
     (λ v,
        match !cache with
        | (w, result) =>
           if w = v then result else (compute v)
        | _ => compute v
        end)
*)

Definition and : expr := λ: λ: if: $0 then $1 else #false.
Definition or : expr := λ: λ: if: $0 then #true else $1.
Definition notb : expr := λ: if: $0 then #false else #true.

(* λ cache, f, v. let res = f v in cache <- (false, v, res); res *)
Definition compute_aux : expr :=
  λ: λ: λ: let: $1 $0 in $3 <- ($1, $0);; $0.

(* λ cache, f, v. let (w, res) = !cache in
                      if v = w
                      then res
                      else compute_L_aux cache f v *)
Definition compute : expr :=
  λ: λ: λ: let: !$2 in
         if: (Proj1 $0 = $1)
         then (Proj2 $0)
         else (compute_aux $3 $2 $1).


Definition mkComputeWithCache : expr :=
  λ: λ:
  let: ref ($0, $1 $0) in
  compute $0 $2.

Definition mkComputeWithCache_aux : expr := App (App mkComputeWithCache $1) $0.

Definition fun_in : sectype :=
  (TNat @ LVar 0 →[H] TNat @ LVar 0) @ L.
Definition fun_out : sectype :=
  fun_in.
Definition init_arg : sectype :=
  TNat @ LVar 0.
Definition mkComputeWithCache_typ : sectype :=
  (fun_in →[L] (init_arg →[L] fun_out ) @L) @ L.


(************************ Proofs ************************)
Definition Ncache : namespace := nroot.@"computeWithCache".

Section bi_defs.
  Context `{!secG Σ}.

  Notation projl Θ := Θ.*2.*1.
  Notation projr Θ := Θ.*2.*2.


  Definition cache_inv
             (Θ : list ((val * val -d> iPropO Σ) * ((val -d> iPropO Σ) * (val -d> iPropO Σ))))
             ρ l1 l2 f τ1 τ2 :=
    (∃ d1 d2 w1 w2, l1 ↦ₗ (d1, w1) ∗ l2 ↦ (d2, w2) ∗
                  ⌜ w1 = f d1 ⌝ ∗ ⌜ w2  = f d2 ⌝ ∗
                  ⌊ τ1 ₗ⌋ₛ (projl Θ) ρ d1 ∗ ⌊ τ2 ᵣ⌋ₛ (projr Θ) ρ d2 ∗
                  ⌊ τ1 ₗ⌋ₛ (projl Θ) ρ w1 ∗ ⌊ τ2 ᵣ⌋ₛ (projr Θ) ρ w2
    )%I.

  Definition is_cache_ref Θ ρ f τ1 τ2 : val * val -d> iPropO Σ := λ vv,
    (∃ l1 l2, ⌜vv.1 = LocV l1⌝ ∗ ⌜vv.2 = LocV l2⌝ ∗ inv Ncache (cache_inv Θ ρ l1 l2 f τ1 τ2))%I.

  Arguments of_val : simpl never.

  Definition isWellBehaved Θ ρ (f1 f2 : expr) (f : val -> val) (τ1 τ2 : sectype) :=
    (<pers> ((∀ v1,  ⌊τ1 ₗ⌋ₛ (projl Θ) ρ v1 -∗ IC@{icd_step_fupd SI_left}  (f1) (#v1) {{w1, ⌜ w1 = (f v1) ⌝ ∗ ⌊τ2 ₗ⌋ₛ (projl Θ)ρ w1 }}) ∗
             (∀ v2,  ⌊τ1 ᵣ⌋ₛ (projr Θ) ρ v2 -∗ IC@{icd_step_fupd SI_right} (f2) (#v2) {{w2, ⌜ w2 = (f v2) ⌝ ∗ ⌊τ2 ᵣ⌋ₛ (projr Θ)ρ w2 }}) ∗
             (∀ v1 v2, ⟦τ1⟧ₛ Θ ρ (v1, v2) -∗ ⟦τ2⟧ₛ Θ ρ (f v1, f v2)))
    )%I.


  Lemma compute_aux_typed Θ ρ f1 f2 f1v f2v f cache1 cache2 :
    envs_Persistent Θ → IntoVal f1 f1v → IntoVal f2 f2v → env_coherent Θ -∗
    is_cache_ref Θ ρ f (TNat @ LVar 0) (TNat @ LVar 0) (cache1, cache2) -∗
    isWellBehaved Θ ρ f1 f2 f (TNat @ LVar 0) (TNat @ LVar 0) -∗
    isWellBehaved Θ ρ (compute_aux (#cache1) f1) (compute_aux (#cache2) f2) f (TNat @ LVar 0) (TNat @ LVar 0).
  Proof.
    iIntros (HPers <- <-) "#HCoh #HisCache (#Hf_typed_l & #Hf_typed_r & #Hf_typed)".
    rewrite /compute_aux !lam_to_val.
    iSplitL; [| iSplitL ].
    - iIntros "!>" (v) "#Hv".
      iApply (ic_step_fupd_bind _ (fill [AppLCtx _; AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|].
      iModIntro; simpl. asimpl. rewrite lam_to_val.
      iApply (ic_value (icd_step_fupd _)); umods. iModIntro.
      iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|]; simpl.
      iModIntro; asimpl.
      iApply (ic_value (icd_step_fupd _)); umods; iModIntro.
      iApply ic_step_fupd_pure_step; [done|]; simpl.
      iModIntro; asimpl.
      iApply (ic_step_fupd_bind _ (fill [LetInCtx _])).
      iApply ic_wand_r; iSplitL.
      { by iApply "Hf_typed_l". }
      iIntros (???) "(-> & #Hf_typed_l')".
      iApply ic_step_fupd_pure_step; [done|]. simpl.
      iModIntro; asimpl.
      iDestruct "HisCache" as (l1 l2) "(%Hl1 & %Hl2 & HcacheInv)".
      simpl in Hl1. rewrite Hl1.
      iApply (ic_step_fupd_bind _ (fill [SeqCtx _])).
      iApply (ic_atomic (icd_step_fupd _) _ StronglyAtomic); try done.
      iInv (Ncache) as "H" "Hclose". iModIntro.
      iDestruct "H" as (????) "(Hl1 & Hl2 & #Hc1 & #Hc2 & #H_typedl & #H_typedr & #H_typedl' & #H_typedr')".
      rewrite !pair_to_val.
      iApply ((@ic_step_fupd_store _ secG_un_left) with "[//]").
      iFrame. iIntros "!> Hl1".
      rewrite /cache_inv.
      iMod ("Hclose" with "[Hl1 Hl2]") as "_".
      {
        iModIntro; iExists _, _, _, _. iFrame.
        iFrame "#"; eauto.
      }
      iApply ic_step_fupd_pure_step; first done.
      do 2 iModIntro.
      iApply ic_value; umods. iModIntro.
      iFrame "#"; eauto.
    - iIntros "!>" (v) "#Hv".
      iApply (ic_step_fupd_bind _ (fill [AppLCtx _; AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|].
      iModIntro; simpl. asimpl. rewrite lam_to_val.
      iApply (ic_value (icd_step_fupd _)); umods. iModIntro.
      iApply (ic_step_fupd_bind _ (fill [AppLCtx _])).
      iApply ic_step_fupd_pure_step; [done|]; simpl.
      iModIntro; asimpl.
      iApply (ic_value (icd_step_fupd _)); umods; iModIntro.
      iApply ic_step_fupd_pure_step; [done|]; simpl.
      iModIntro; asimpl.
      iApply (ic_step_fupd_bind _ (fill [LetInCtx _])).
      iApply ic_wand_r; iSplitL.
      { by iApply "Hf_typed_r". }
      iIntros (???) "(-> & #Hf_typed_r')".
      iApply ic_step_fupd_pure_step; [done|]; simpl.
      iModIntro; asimpl.
      iDestruct "HisCache" as (l1 l2) "(%Hl1 & %Hl2 & HcacheInv)".
      simpl in Hl2. rewrite Hl2.
      iApply (ic_step_fupd_bind _ (fill [SeqCtx _])).
      iApply (ic_atomic (icd_step_fupd _) _ StronglyAtomic); try done.
      iInv (Ncache) as "H" "Hclose". iModIntro.
      iDestruct "H" as (????) "(Hl1 & Hl2 & #Hc1 & #Hc2 & #H_typedl & #H_typedr & #H_typedl' & #H_typedr')".
      rewrite !pair_to_val.
      iApply ((@ic_step_fupd_store _ secG_un_right) with "[//]").
      iFrame. iIntros "!> Hl2".
      rewrite /cache_inv.
      iMod ("Hclose" with "[Hl1 Hl2]") as "_".
      {
        iModIntro; iExists _, _, _, _. iFrame.
        iFrame "#"; eauto.
      }
      iApply ic_step_fupd_pure_step; first done.
      do 2 iModIntro.
      iApply ic_value; umods. iModIntro.
      iFrame "#"; eauto.
    - iIntros "!>" (v1 v2) "#Hvv".
      by iApply "Hf_typed".
  Qed.

  Definition is_closed (f : expr) := ∀ σ, f.[σ] = f.

  Lemma compute_aux_closed :
    is_closed compute_aux.
  Proof. rewrite /is_closed. autosubst. Qed.

  Lemma loc_closed (ι : loc) :
    is_closed (# ι).
  Proof. rewrite /is_closed. autosubst. Qed.

  Hint Rewrite compute_aux_closed : autosubst.
  Hint Rewrite loc_closed : autosubst.
  Opaque compute_aux.

  Lemma compute_typed Θ ρ f1 f2 f1v f2v f cache1 cache2 :
    envs_Persistent Θ → IntoVal f1 f1v → IntoVal f2 f2v → is_closed (#f1v) → is_closed (#f2v) →
    env_coherent Θ -∗
    is_cache_ref Θ ρ f (TNat @ LVar 0) (TNat @ LVar 0) (cache1, cache2) -∗
    isWellBehaved Θ ρ f1 f2 f (TNat @ LVar 0) (TNat @ LVar 0) -∗
    ⟦ fun_out ⟧ₑ Θ ρ (compute (#cache1) (#f1v)
                    , compute (#cache2) (#f2v)).
  Proof.
    iIntros (HPers Hv1 Hv2 Hcl1 Hcl2) "#HCoh #isCache #isWellBehaved".
    iPoseProof (compute_aux_typed with "HCoh isCache isWellBehaved") as "(HrecomputeL & HrecomputeR & Hrecompute)".
    iDestruct "isCache" as (l1 l2) "/= (-> & -> & HcacheInv)".
    rewrite /compute !lam_to_val.
    iApply (ic_left_strong_bind _ _ (fill [ AppLCtx _ ]) (fill [ AppLCtx _ ])).
    iApply ic_left_pure_step; first done.
    iApply ic_left_pure_step_index; first done.
    iModIntro. simpl.
    rewrite !compute_aux_closed. asimpl.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    iModIntro. asimpl.
    iApply ic_left_pure_step; first done.
    iApply ic_left_pure_step_index; first done.
    iModIntro. simpl. asimpl.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    iModIntro; asimpl.
    rewrite [⟦ fun_out ⟧ₛ _ _ ((λ: _ )%V, (λ: _)%V)] interp_sec_def /= bool_decide_eq_true_2 //.
    rewrite interp_arrow_def.
    iSplitL.
    - iIntros "!>" (vv) "#Hvv".
      iApply ic_left_pure_step; first done.
      iApply ic_left_pure_step_index; first done.
      iModIntro. asimpl.
      iApply (ic_left_strong_bind _ _ (fill [ LetInCtx _ ]) (fill [ LetInCtx _ ])).
      iApply (ic_double_atomic_lr _ _ StronglyAtomic).
      iInv (Ncache) as "H" "Hclose". iModIntro. rewrite /cache_inv.
      iDestruct "H" as (????) "(Hl1 & Hl2 & #Hc1 & #Hc2 & #H_typedl & #H_typedr & #H_typedl' & #H_typedr')".
      iApply ((@ic_step_fupd_load _ secG_un_left)); [done|].
      iFrame. iIntros "!> Hl1".
      iApply ((@ic_fupd_load _ secG_un_right)); [done|].
      iFrame. iIntros "Hl2 /=". rewrite !Hcl1 !Hcl2.
      iMod ("Hclose" with "[-]") as "_".
      { iNext. iExists _,_,_,_. iFrame. iFrame "#". }
      iModIntro. cbn.
      iApply ic_left_pure_step; first done.
      iApply ic_left_pure_step_index; first done.
      iModIntro. rewrite /= !compute_aux_closed !Hcl1 !Hcl2. asimpl.
      iApply (ic_left_strong_bind _ _ (fill [ BinOpLCtx _ _; IfCtx _ _ ]) (fill [ BinOpLCtx _ _; IfCtx _ _ ])).
      rewrite [⟦ TNat @ _ ⟧ₛ _ _ _]interp_sec_def interp_nat_def !interp_un_sec_def !interp_un_nat_def /=.
      case_bool_decide as Hflows.
      {
        iApply ic_left_pure_step; first done.
        iApply ic_left_pure_step_index; first done.
        iModIntro. iApply ic_value; umods.
        iApply (ic_value ic_right); umods. iModIntro.
        iApply (ic_left_strong_bind _ _ (fill [ IfCtx _ _ ]) (fill [ IfCtx _ _ ])).
        iDestruct "Hvv" as (n1 n2) "(-> & -> & ->)".
        iDestruct "H_typedl" as (H') "->".
        iDestruct "H_typedr" as (H0') "->".
        iDestruct "H_typedl'" as (H1') "->".
        iDestruct "H_typedr'" as (H2') "->".
        iApply ic_left_pure_step; first done.
        iApply ic_left_pure_step_index; first done.
        iModIntro. simpl.
        case_bool_decide as Heql; case_bool_decide as Heqr.
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro. cbn.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iApply ic_value; umods.
          iApply (ic_value ic_right); umods.
          do 2 iModIntro.
          iDestruct "Hc1" as "->"; iDestruct "Hc2" as "->".
          iApply "Hrecompute"; subst.
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists _, _.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro. cbn.
          iApply ic_un_bi_lr.
          iApply ic_wand_r; iSplitL.
          { rewrite Hv1. iApply "HrecomputeL". by iExists _. }
          iIntros (???) "(-> & #Hrecomputed)".
          iApply ic_step_fupd_pure_step; first done.
          iApply ic_value; umods.
          do 2 iModIntro. iDestruct "Hc2" as "->".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists _, _.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro; cbn.
          iApply ic_un_bi_lr.
          iApply ic_step_fupd_pure_step; first done.
          iModIntro. iApply ic_value; umods. iModIntro.
          iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
          { rewrite Hv2. iApply "HrecomputeR". by iExists _. }
          iIntros (???) "(-> & #Hrecomputed)".
          iDestruct "Hc1" as "->".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists _, _.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro; cbn.
          iApply ic_un_bi_lr.
          iApply ic_wand_r; iSplitL.
          { rewrite Hv1. iApply "HrecomputeL". by iExists _. }
          iIntros (???) "(-> & #HrecomputedL)".
          iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
          { rewrite Hv2. iApply "HrecomputeR". by iExists _. }
          iIntros (???) "(-> & #HrecomputedR) /=".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists _, _.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
      }
      {
        iApply ic_left_pure_step; first done.
        iApply ic_left_pure_step_index; first done.
        iModIntro. iApply ic_value; umods.
        iApply (ic_value ic_right); umods. iModIntro.
        iApply (ic_left_strong_bind _ _ (fill [ IfCtx _ _ ]) (fill [ IfCtx _ _ ])).
        iDestruct "Hvv" as "(Hv1 & Hv2)".
        iDestruct "Hv1" as  (v1) "->".
        iDestruct "Hv2" as  (v2) "->".
        iDestruct "H_typedl" as (H') "->".
        iDestruct "H_typedr" as (H0') "->".
        iDestruct "H_typedl'" as (H1') "->".
        iDestruct "H_typedr'" as (H2') "->".
        iApply ic_left_pure_step; first done.
        iApply ic_left_pure_step_index; first done.
        iModIntro. simpl.
        case_bool_decide as Heql; case_bool_decide as Heqr.
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro. cbn.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iApply ic_value; umods.
          iApply (ic_value ic_right); umods.
          do 2 iModIntro.
          iDestruct "Hc1" as "->"; iDestruct "Hc2" as "->".
          iApply "Hrecompute"; subst.
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists v1, v2.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro. cbn.
          iApply ic_un_bi_lr.
          iApply ic_wand_r; iSplitL.
          { rewrite Hv1. iApply "HrecomputeL". by iExists _. }
          iIntros (???) "(-> & #Hrecomputed)".
          iApply ic_step_fupd_pure_step; first done.
          iApply ic_value; umods.
          do 2 iModIntro. iDestruct "Hc2" as "->".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists v1, v2.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro; cbn.
          iApply ic_un_bi_lr.
          iApply ic_step_fupd_pure_step; first done.
          iModIntro. iApply ic_value; umods. iModIntro.
          iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
          { rewrite Hv2. iApply "HrecomputeR". by iExists _. }
          iIntros (???) "(-> & #Hrecomputed)".
          iDestruct "Hc1" as "->".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          + rewrite interp_nat_def. by iExists v1, v2.
          + iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
        - iApply (ic_value ic_binary); umods.
          iApply (ic_value ic_right); umods. iModIntro.
          iApply ic_left_pure_step; first done.
          iApply ic_left_pure_step_index; first done.
          iModIntro; cbn.
          iApply ic_un_bi_lr.
          iApply ic_wand_r; iSplitL.
          { rewrite Hv1. iApply "HrecomputeL". by iExists _. }
          iIntros (???) "(-> & #HrecomputedL)".
          iApply (ic_wand_r (icd_step_fupd _)); iSplitL.
          { rewrite Hv2. iApply "HrecomputeR". by iExists _. }
          iIntros (???) "(-> & #HrecomputedR) /=".
          iApply "Hrecompute".
          rewrite [⟦ TNat @ §0 ⟧ₛ _ _ _] interp_sec_def /=. case_bool_decide.
          * rewrite interp_nat_def. by iExists v1, v2.
          * iSplitL; (rewrite interp_un_sec_def interp_un_nat_def; by iExists _).
      }
    - iSplitL; simpl; rewrite interp_un_arrow_def.
      + iIntros "!>" (v1) "#Hv1 %".
        iApply ic_step_fupd_pure_step; first done.
        rewrite !Hcl1. iModIntro; asimpl.
        iApply (ic_step_fupd_bind _ (fill [LetInCtx _])).
        iApply (ic_atomic (icd_step_fupd _) _ StronglyAtomic); try done.
        iInv (Ncache) as "H" "Hclose". iModIntro.
        iDestruct "H" as (????) "(Hl1 & Hl2 & #Hc1 & #Hc2 & #H_typedl & #H_typedr & #H_typedl' & #H_typedr')".
        iApply ((@ic_step_fupd_load _ secG_un_left) with "[//]").
        iFrame. iIntros "!> Hl1".
        rewrite /cache_inv.
        iMod ("Hclose" with "[Hl1 Hl2]") as "_".
        {
          iModIntro; iExists _, _, _, _. iFrame.
            by iFrame "#".
        }
        iApply ic_step_fupd_pure_step; first done.
        do 2 iModIntro. rewrite !Hcl1. asimpl.
        iApply (ic_step_fupd_bind _ (fill [ IfCtx _ _ ])).
        rewrite !interp_un_sec_def !interp_un_nat_def.
        iDestruct "H_typedl" as (H') "->".
        iDestruct "H_typedl'" as (H1') "->".
        iDestruct "Hv1" as (v1') "->".
        iApply (ic_step_fupd_bind _ (fill [ BinOpLCtx _ _ ])).
        iApply ic_step_fupd_pure_step; first done.
        iApply ic_value; umods. do 2 iModIntro.
        iApply ic_step_fupd_pure_step; first done.
        iApply ic_value; umods. do 2 iModIntro.
        case_bool_decide.
        * iApply ic_step_fupd_pure_step; first done.
          iApply ic_step_fupd_pure_step; first done.
          iApply ic_value; umods. do 3 iModIntro; subst.
          by iExists _.
        * iApply ic_step_fupd_pure_step; first done.
          rewrite !Hcl1 Hv1.
          iApply ic_wand_r; iSplitL.
          { iApply "HrecomputeL". iModIntro. by iExists _. }
          iIntros "!>" (???) "(-> & #Hrecomputed') //".
      + iIntros "!>" (v2) "#Hv2 %".
        iApply ic_step_fupd_pure_step; first done.
        rewrite !Hcl2. iModIntro; asimpl.
        iApply (ic_step_fupd_bind _ (fill [LetInCtx _])).
        iApply (ic_atomic (icd_step_fupd _) _ StronglyAtomic); try done.
        iInv (Ncache) as "H" "Hclose". iModIntro.
        iDestruct "H" as (????) "(Hl1 & Hl2 & #Hc1 & #Hc2 & #H_typedl & #H_typedr & #H_typedl' & #H_typedr')".
        iApply ((@ic_step_fupd_load _ secG_un_right) with "[//]").
        iFrame. iIntros "!> Hl2".
        rewrite /cache_inv.
        iMod ("Hclose" with "[Hl1 Hl2]") as "_".
        {
          iModIntro; iExists _, _, _, _. iFrame.
            by iFrame "#".
        }
        iApply ic_step_fupd_pure_step; first done.
        do 2 iModIntro. rewrite !Hcl2. asimpl.
        iApply (ic_step_fupd_bind _ (fill [ IfCtx _ _ ])).
        rewrite !interp_un_sec_def !interp_un_nat_def.
        iDestruct "H_typedr" as (H') "->".
        iDestruct "H_typedr'" as (H1') "->".
        iDestruct "Hv2" as (v2') "->".
        iApply (ic_step_fupd_bind _ (fill [ BinOpLCtx _ _ ])).
        iApply ic_step_fupd_pure_step; first done.
        iApply ic_value; umods. do 2 iModIntro.
        iApply ic_step_fupd_pure_step; first done.
        iApply ic_value; umods. do 2 iModIntro.
        case_bool_decide.
        * iApply ic_step_fupd_pure_step; first done.
          iApply ic_step_fupd_pure_step; first done.
          iApply ic_value; umods. do 3 iModIntro; subst.
          by iExists _.
        * iApply ic_step_fupd_pure_step; first done.
          rewrite !Hcl2 Hv2.
          iApply ic_wand_r; iSplitL.
          { iApply "HrecomputeR". iModIntro. by iExists _. }
          iIntros "!>" (???) "(-> & #Hrecomputed') //".
  Qed.

  Lemma compute_with_cache_typed Θ ρ f1 f2 f1v f2v f :
    envs_Persistent Θ → IntoVal f1 f1v → IntoVal f2 f2v →is_closed (#f1v) → is_closed (#f2v) →
    env_coherent Θ -∗
    isWellBehaved Θ ρ f1 f2 f (TNat @ LVar 0) (TNat @ LVar 0) -∗
    ⟦ fun_out ⟧ₑ Θ ρ (mkComputeWithCache (#f1v) 0
                    , mkComputeWithCache (#f2v) 0).
  Proof.
    iIntros (Hpers Hv1 Hv2 Hcl1 Hcl2) "#HCoh #HisWellbehaved".
    rewrite /mkComputeWithCache /mkComputeWithCache !lam_to_val.
    iApply (ic_left_strong_bind _ _ (fill [ AppLCtx _ ]) (fill [ AppLCtx _ ])).
    iApply ic_left_pure_step; first done.
    iApply ic_left_pure_step_index; first done.
    iModIntro. simpl. asimpl.
    iApply (ic_value ic_binary); umods.
    iApply (ic_value ic_right); umods.
    iModIntro.
    iApply ic_left_pure_step; first done.
    iApply ic_left_pure_step_index; first done.
    iModIntro. rewrite !Hcl1 !Hcl2. asimpl.
    iApply (ic_left_strong_bind _ _ (fill [ LetInCtx _ ]) (fill [ LetInCtx _ ])).
    rewrite !nat_to_val.
    iApply (ic_left_strong_bind _ _ (fill [  PairRCtx _; AllocCtx ]) (fill [ PairRCtx _; AllocCtx ])).
    iDestruct "HisWellbehaved" as "(#Hf_typed_l & #Hf_typed_r & #Hf_typed)".
    rewrite !Hcl1 !Hcl2 Hv1 Hv2.
    iApply ic_un_bi_lr.
    iApply ic_wand_r; iSplitL.
    { iApply "Hf_typed_l". by iExists _.  }
    iIntros (???) "( -> & #Hf_typed_l' )".
    iApply ic_wand_r; iSplitL.
    { iApply "Hf_typed_r". by iExists _.  }
    iIntros (???) "( -> & #Hf_typed_r' ) /=".
    iApply ic_un_bi_lr. rewrite !pair_to_val.
    iApply ((@ic_step_fupd_alloc _ secG_un_left) with "[//]").
    iNext. iIntros (ι1) "Hι1".
    iApply ic_fupd.
    iApply ((@ic_step_fupd_alloc _ secG_un_right) with "[//]").
    iNext. iIntros (ι2) "Hι2"; cbn.
    iMod (inv_alloc Ncache _ (cache_inv _ _ ι1 ι2 f _ _) with "[-]") as "#HisCache".
    {
      iModIntro. rewrite /cache_inv.
      iExists _, _, _, _. iFrame. iFrame "#". repeat iSplitL; try done.
      all: by iExists _.
    }
    iApply ic_left_pure_step; first done.
    iApply ic_left_pure_step_index; first done.
    iModIntro. asimpl.
    iPoseProof ((compute_typed _ _ f1 f2) with "HCoh") as "compute_typed"; [done|done|].
    rewrite -!Hv1 !Hcl1 -!Hv2 !Hcl2 Hv1 Hv2.
    iApply "compute_typed".
    - rewrite /is_cache_ref.
      iExists _, _; eauto.
    - rewrite /isWellBehaved. do 2 iModIntro. iFrame "#".
  Qed.

End bi_defs.
