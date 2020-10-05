From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Section typed.
  Context `{!SecurityLattice label}.

  (* [ℓ] is the label of the elements *)
  Definition list (t : type) (ℓ : label_term) : sectype :=
    TRec ((TUnit @ ⊥ₛ) + ((t @ ℓ) * ($0 @ ⊥ₛ) @ ⊥ₛ) @ ⊥ₛ) @ ⊥ₛ.

  Definition TList : sectype :=
    (∀ₗ: ⊤ₛ; (∀ₜ: ⊤ₛ; (list $1 §0)) @ ⊥ₛ) @ ⊥ₛ.

  Definition nil : expr :=
    Λₗ: Λₜ: Fold (InjL ()%V).
  Definition cons : expr :=
    Λₗ: Λₜ: λ: λ: Fold (InjR ($1, $0)).
  Definition head : expr :=
    λ: λ:
       match: Unfold ($1) with
         InjL => $1 (* empty *)
       | InjR => Proj1 $0
       end.
  Definition tail : expr :=
    λ:
       match: Unfold ($0) with
         InjL => $1 (* empty *)
       | InjR => Proj2 $0
       end.

  Lemma nil_typed Γ pc :
    Γ # pc ⊢ₜ nil : TList.
  Proof. do 3 econstructor. asimpl. do 2 constructor. Qed.

  Lemma nil_app_typed Γ pc t ℓ :
    Γ # pc ⊢ₜ (nil <_>ₗ <_>ₜ)%E : list t.[ren (+1)] ℓ.
  Proof.
    epose proof (TApp_typed _ _ _ (list $1 ℓ) t ⊥ₛ ⊤ₛ) as Htapp.
    asimpl in Htapp.
    eapply Htapp; try by repeat constructor.
    clear Htapp.
    epose proof (TLApp_typed _ _ _ ((∀ₜ: ⊤ₛ; list $1 §0) @ ⊥ₛ) ⊥ₛ ℓ ⊤ₛ) as Hlapp.
    eapply Hlapp; try by repeat constructor.
  Qed.

  Definition cons_typ : type :=
    ∀ₗ: ⊤ₛ; (∀ₜ: ⊤ₛ; ($0 @ §0 →[⊤ₛ] (list $1 §0 →[⊤ₛ] list $1 §0) @ ⊥ₛ) @ ⊥ₛ) @ ⊥ₛ.

  Lemma cons_typed Γ pc :
    Γ # pc ⊢ₜ cons : cons_typ @ ⊥ₛ.
  Proof. do 5 econstructor. asimpl. do 4 econstructor. Qed.

  Lemma cons_app_typed Γ pc t ℓ x xs :
    Γ # pc ⊢ₜ x : t @ ℓ →
    Γ # pc ⊢ₜ xs : list t.[ren (+1)] ℓ →
    Γ # pc ⊢ₜ (cons <_>ₗ <_>ₜ x xs)%E : list t.[ren (+1)] ℓ.
  Proof.
    move=> Hx Hxs.
    eapply (App_typed _ _ _ _ _ _ _ ⊤ₛ); try by repeat constructor.
    eapply (App_typed _ _ _ _ _ _ _ ⊤ₛ); try by repeat constructor.
    epose proof (TApp_typed _ _ _
      (($0 @ ℓ →[⊤ₛ] (list $1 ℓ →[⊤ₛ] list $1 ℓ) @ ⊥ₛ) @ ⊥ₛ) t ⊥ₛ ⊤ₛ) as Htapp.
    asimpl in Htapp.
    eapply Htapp; try by repeat constructor.
    clear Htapp.
    epose proof (TLApp_typed _ _ _
      ((∀ₜ: ⊤ₛ; ($0 @ §0 →[⊤ₛ] (list $1 §0 →[⊤ₛ] list $1 §0) @ ⊥ₛ) @ ⊥ₛ) @ ⊥ₛ) ⊥ₛ ℓ ⊤ₛ) as Hlapp.
    asimpl in Hlapp.
    eapply Hlapp; try by repeat constructor.
  Qed.

  Lemma head_typed Γ pc t ℓ default xs :
    Γ # pc ⊢ₜ xs : list t.[ren (+1)] ℓ →
    Γ # pc ⊢ₜ default : t @ ℓ →
    Γ # pc ⊢ₜ head xs default : t @ ℓ.
  Proof.
    move=> Hxs Hdef.
    eapply (App_typed _ _ _ _ _ _ _ ⊤ₛ); try (done||by repeat constructor).
    eapply (App_typed _ _ _ _ _ _ _ ⊤ₛ); try (done||by repeat constructor).
    rewrite /head.
    eapply (Sub_typed _ _ _ _ (_ @ ⊥ₛ)); [|reflexivity|]; last first.
    { econstructor; [|reflexivity]. constructor. }
    econstructor.
    eapply (Sub_typed _ _ _ _ (_ @ ⊥ₛ)); [|reflexivity|]; last first.
    { econstructor; [|reflexivity]. constructor. }
    do 2 econstructor.
       - epose proof (TUnfold _ _ _ (_ + _ @ _) _) as H. asimpl in H.
         eapply H; by econstructor.
       - by constructor.
       - asimpl. eapply (Proj1_typed _ _ _ _ _ ⊥ₛ); by constructor.
       - by constructor.
  Qed.

  Lemma tail_typed Γ pc t ℓ xs :
    Γ # pc ⊢ₜ xs : list t.[ren (+1)] ℓ →
    Γ # pc ⊢ₜ tail xs: list t.[ren (+1)] ℓ.
  Proof.
    move=> Hxs.
    eapply (App_typed _ _ _ _ _ _ _ ⊤ₛ); try (done||by repeat constructor).
    rewrite /tail.
    eapply (Sub_typed _ _ _ _ (_ @ ⊥ₛ)); [|reflexivity|]; last first.
    { econstructor; [|reflexivity]. constructor. }
    econstructor.
    eapply (Sub_typed _ _ _ _ (_ @ ⊥ₛ)); [|reflexivity|]; last first.
    { econstructor; [|reflexivity]. constructor. }
    do 2 econstructor; try done.
       - epose proof (TUnfold _ _ _ (_ + _ @ _) _) as H. asimpl in H.
         eapply H; by econstructor.
       - by constructor.
       - asimpl. done.
  Qed.

End typed.

Section specs.
 Context `{!secG Σ, !SecurityLattice label}.

 Lemma head_spec Θ ρ t ℓ x xs x' xs' :
    ⟦ t @ ℓ ⟧ₛ Θ ρ (x, x') -∗
    ⟦ list t.[ren (+1)] ℓ ⟧ₛ Θ ρ (xs, xs') -∗
    ⟦ t @ ℓ ⟧ₑ Θ ρ (head (#xs) (#x), head (#xs') (#x')).
 Proof.
   iIntros "Hx Hxs".
   rewrite /interp_expr /head /= .
   iApply (mwp_left_strong_bind _ _ (fill [AppLCtx _]) (fill [AppLCtx _])).
   iApply mwp_left_pure_step; [done|].
   iApply mwp_left_pure_step_index; [done|].
   iModIntro. asimpl.
   iApply (mwp_value mwp_binary); umods.
   iApply (mwp_value (mwpd_right _)); umods.
   iModIntro.
   iApply mwp_left_pure_step; [done|].
   iApply mwp_left_pure_step_index; [done|].
   iModIntro. asimpl.
   rewrite [⟦ list _ _ ⟧ₛ _ _ _]interp_sec_def /=.
   rewrite bool_decide_eq_true_2; last apply ord_bottom.
   rewrite interp_rec_def fixpoint_interp_rec1_eq /interp_rec1 /=.
   iDestruct "Hxs" as ([w1 w2]) "[% #Hxs]". simplify_eq.
   rewrite -interp_rec_def /=.
   iApply (mwp_left_strong_bind _ _ (fill [CaseCtx _ _]) (fill [CaseCtx _ _])); cbn.
   iApply mwp_left_pure_step; [done|].
   iApply mwp_left_pure_step_index; [done|].
   iApply (mwp_value mwp_binary); umods.
   iApply (mwp_value (mwpd_right _)); umods.
   rewrite [⟦ _ + _ @ _⟧ₛ _ _ _]interp_sec_def
           bool_decide_eq_true_2; last apply ord_bottom.
   do 2 iModIntro.
   rewrite interp_sum_def.
   iDestruct "Hxs" as (??) "[(% & Hxs) | (% & Hxs)]"; simplify_eq.
   - iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|].
     rewrite -/of_val. asimpl.
     iApply (mwp_value mwp_binary); umods.
     iApply (mwp_value (mwpd_right _)); umods.
     done.
   - iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|].
     rewrite -/of_val. asimpl.
     rewrite [⟦ _ * _ @ _⟧ₛ _ _ _]interp_sec_def
             bool_decide_eq_true_2; last apply ord_bottom.
     rewrite interp_prod_def /=.
     iDestruct "Hxs" as (????) "(-> & -> & Hhead & _)".
     iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|]. rewrite -/of_val.
     iApply (mwp_value mwp_binary); umods.
     iApply (mwp_value (mwpd_right _)); umods.
     do 3 iModIntro.
     by iApply (interp_sec_type_weaken _ [] [_] _ 0).
  Qed.

 Lemma tail_spec Θ ρ t ℓ xs xs' :
    ⟦ list t.[ren (+1)] ℓ ⟧ₛ Θ ρ (xs, xs') -∗
    ⟦ list t.[ren (+1)] ℓ ⟧ₑ Θ ρ (tail (#xs), tail (#xs')).
 Proof.
   iIntros "Hxs".
   rewrite /interp_expr /tail /= .
   iApply mwp_left_pure_step; [done|].
   iApply mwp_left_pure_step_index; [done|].
   iModIntro. asimpl.
   rewrite [⟦ list _ _ ⟧ₛ _ _ _]interp_sec_def /=.
   rewrite bool_decide_eq_true_2; last apply ord_bottom.
   rewrite interp_rec_def fixpoint_interp_rec1_eq /interp_rec1 /=.
   iDestruct "Hxs" as ([w1 w2]) "[% #Hxs]". simplify_eq.
   rewrite -interp_rec_def /=.
   iApply (mwp_left_strong_bind _ _ (fill [CaseCtx _ _]) (fill [CaseCtx _ _])); cbn.
   iApply mwp_left_pure_step; [done|].
   iApply mwp_left_pure_step_index; [done|].
   iApply (mwp_value mwp_binary); umods.
   iApply (mwp_value (mwpd_right _)); umods.
   rewrite [⟦ _ + _ @ _⟧ₛ _ _ _]interp_sec_def
           bool_decide_eq_true_2; last apply ord_bottom.
   do 2 iModIntro.
   rewrite interp_sum_def.
   iDestruct "Hxs" as (??) "[(% & Hxs) | (% & Hxs)]"; simplify_eq.
   - iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|].
     rewrite -/of_val. asimpl.
     iApply (mwp_value mwp_binary); umods.
     iApply (mwp_value (mwpd_right _)); umods.
     do 2 iModIntro. rewrite /list.
     rewrite (interp_sec_def _ _ _ (FoldV _, FoldV _)) bool_decide_eq_true_2; last apply ord_bottom.
     rewrite interp_rec_def fixpoint_interp_rec1_eq /interp_rec1 //=.
     iModIntro. iExists ((InjLV _), (InjLV _)). iSplit; try done. iModIntro.
     rewrite (interp_sec_def _ _ (TSum _ _ @ _) ) bool_decide_eq_true_2; last apply ord_bottom.
     rewrite interp_sum_def.
     iExists _, _. iLeft; iSplit; try done.
   - iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|].
     rewrite -/of_val. asimpl.
     rewrite [⟦ _ * _ @ _⟧ₛ _ _ _]interp_sec_def
             bool_decide_eq_true_2; last apply ord_bottom.
     rewrite interp_prod_def /=.
     iDestruct "Hxs" as (????) "(-> & -> & _ & Htail)".
     iApply mwp_left_pure_step; [done|].
     iApply mwp_left_pure_step_index; [done|]. rewrite -/of_val.
     iApply (mwp_value mwp_binary); umods.
     iApply (mwp_value (mwpd_right _)); umods.
     do 3 iModIntro.
     rewrite interp_sec_def bool_decide_eq_true_2; last apply ord_bottom.
     rewrite interp_tvar_def //= /list.
     by rewrite interp_sec_def bool_decide_eq_true_2; last apply ord_bottom.
  Qed.

End specs.

Section NatList.
  Context `{!secG Σ, !SecurityLattice label}.

  (* NatList *)
  Definition TNatList ℓ := list TNat ℓ.

  Notation nil_nat := (nil <_>ₗ <_>ₜ)%E.
  Notation cons_nat := (cons <_>ₗ <_>ₜ)%E.

  Lemma nil_nat_typed Γ pc ℓ :
    Γ # pc ⊢ₜ nil_nat : TNatList ℓ.
  Proof. apply (nil_app_typed _ _ TNat). Qed.

  Lemma cons_nat_typed Γ pc ℓ x xs :
    Γ # pc ⊢ₜ x : TNat @ ℓ →
    Γ # pc ⊢ₜ xs : TNatList ℓ →
    Γ # pc ⊢ₜ (cons_nat x xs)%E : TNatList ℓ.
  Proof. apply (cons_app_typed _ _ TNat). Qed.

  Lemma head_nat_typed Γ pc ℓ default xs :
    Γ # pc ⊢ₜ xs : TNatList ℓ →
    Γ # pc ⊢ₜ default : TNat @ ℓ →
    Γ # pc ⊢ₜ head xs default : TNat @ ℓ.
  Proof. apply (head_typed _ _ TNat). Qed.

  Lemma head_nat_spec Θ ρ ℓ x xs x' xs' :
    ⟦ TNat @ ℓ ⟧ₛ Θ ρ (x, x') -∗
    ⟦ TNatList ℓ ⟧ₛ Θ ρ (xs, xs') -∗
    ⟦ TNat @ ℓ ⟧ₑ Θ ρ (head (#xs) (#x), head (#xs') (#x')).
  Proof. apply head_spec. Qed.

  Lemma tail_nat_typed Γ pc ℓ xs :
    Γ # pc ⊢ₜ xs : TNatList ℓ →
    Γ # pc ⊢ₜ tail xs : TNatList ℓ.
  Proof. apply (tail_typed _ _ TNat). Qed.

  Lemma tail_nat_spec Θ ρ ℓ xs xs' :
    ⟦ TNatList ℓ ⟧ₛ Θ ρ (xs, xs') -∗
    ⟦ TNatList ℓ ⟧ₑ Θ ρ (tail (#xs), tail (#xs')).
  Proof. eapply (tail_spec _ _ TNat). Qed.
End NatList.

Notation nil_nat := (nil <_>ₗ <_>ₜ)%E.
Notation cons_nat := (cons <_>ₗ <_>ₜ)%E.
