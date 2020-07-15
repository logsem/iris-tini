From iris.bi Require Import bi.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op.
From iris.proofmode Require Export classes tactics coq_tactics.

Import bi.

(* future modality *)
Definition future_def `{!BiFUpd PROP}
    (E : coPset) n (P : PROP) : PROP :=
  (Nat.iter n (λ Q, (|={E}=> ▷ Q)) (|={E}=> P))%I.
Definition future_aux : { x | x = @future_def }. by eexists. Qed.
Definition future := proj1_sig future_aux.
Definition future_eq : @future = @future_def := proj2_sig future_aux.
Arguments future {_ _} _ _ _%I.
Instance: Params (@future) 4 := {}.

Notation "|≫{ E }=[ n ]=> Q" := (future E n Q)
  (at level 99, E at level 50, Q at level 200,
   format "|≫{ E }=[ n ]=>  Q") : bi_scope.
Notation "P ≫{ E }=[ n ]=∗ Q" := (P -∗ |≫{E}=[n]=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ≫{ E }=[ n ]=∗  Q") : bi_scope.
Notation "P ≫{ E }=[ n ]=∗ Q" := (P ⊢ |≫{E}=[n]=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : stdpp_scope.


Lemma future_unfold `{!BiFUpd PROP} (E : coPset) n (P : PROP) :
  (|≫{E}=[n]=> P) ⊣⊢
  (match n with
   | O => |={E}=> P
   | S n => (Nat.iter (S n) (λ Q, (|={E}=> ▷ Q)) (|={E}=> P))
   end).
Proof.
  rewrite future_eq. destruct n; trivial.
Qed.

Lemma future_unfold_O `{!BiFUpd PROP} (E : coPset) (P : PROP) :
  (|≫{E}=[0]=> P) ⊣⊢ |={E}=> P.
Proof. by rewrite future_unfold. Qed.

Lemma future_unfold_S `{!BiFUpd PROP} (E : coPset) n (P : PROP) :
  (|≫{E}=[S n]=> P) ⊣⊢ |={E}=> ▷ (|≫{E}=[n]=> P).
Proof. by rewrite !future_unfold /=; destruct n; simpl. Qed.

Section future_and_plain.
 Context `{!BiFUpd PROP} `{BiPlainly PROP} `{BiFUpdPlainly PROP}.

 Implicit Types P Q : PROP.

 Lemma fupd_extract_plain' {E1 E2 E2'} P Q `{!Plain P} :
   E1 ⊆ E2 →
  (Q ={E1, E2'}=∗ P) → (|={E1, E2}=> Q) ⊢ |={E1}=> ((|={E1, E2}=> Q) ∗ P).
 Proof.
   iIntros (HE HQP) "HQ".
   iMod (fupd_plain_keep_r E1 P (|={E1,E2}=> Q) with "[$HQ]")%I; last by eauto.
   iIntros "HQ".
   apply subseteq_disjoint_union_L in HE; destruct HE as [E3 [? HE]]; subst.
   iApply fupd_plain_mask.
   iMod "HQ"; iPoseProof (HQP with "HQ") as "HP".
   iApply (fupd_mask_frame _ _ E1); first set_solver.
   iMod (fupd_plain_mask with "HP") as "$"; by repeat iModIntro.
 Qed.

 Lemma fupd_extract_plain {E1 E2} P Q `{!Plain P} :
   E1 ⊆ E2 →
  (Q ⊢ P) → (|={E1, E2}=> Q) ⊢ |={E1}=> ((|={E1, E2}=> Q) ∗ P).
 Proof.
   iIntros (HE HQP) "HQ".
   iApply (fupd_extract_plain' with "HQ"); auto.
   by iIntros "?"; iModIntro; iApply HQP.
 Qed.

 Lemma step_Sn_fupd_mono {E} P Q n :
   (P ⊢ Q) →
   Nat.iter n (λ Q, |={E}=> ▷ Q) P ⊢ Nat.iter n (λ Q, |={E}=> ▷ Q) Q.
 Proof.
  revert P Q; induction n=> P Q HPQ; first done.
  rewrite !Nat_iter_S_r; apply IHn. iIntros "HP".
  iMod "HP"; iModIntro; iNext; by iApply HPQ.
 Qed.

 Lemma future_plain_base {E} P `{Hpl: !Plain P} n :
   (Nat.iter (S n) (λ Q, (|={E}=> ▷ Q)) (|={E}=> P)) ⊢
   |={E}=> Nat.iter (S n) (λ Q, ▷ ◇ Q) P.
 Proof.
  revert P Hpl. induction n=> P Hpl.
  - simpl. iIntros "HP"; iMod "HP".
    by iApply fupd_plainly_later; rewrite -(plain P).
  - rewrite !(Nat_iter_S_r (S n)). iIntros "Hfpn".
    iApply IHn. iApply step_Sn_fupd_mono; last trivial.
    iIntros "HP"; iMod "HP".
    by iApply fupd_plainly_later; rewrite -(plain P).
 Qed.

 Lemma future_S {E} P n : (|≫{E}=[S n]=> P) ⊣⊢ |={E}=> ▷ (|≫{E}=[n]=> P).
 Proof. by rewrite !future_eq. Qed.

 Lemma future_mono {E} Q P n :
  (Q ⊢ P) → (|≫{E}=[n]=> Q) ⊢ (|≫{E}=[n]=> P).
  Proof.
    revert Q P; induction n => Q P HQP.
    - by rewrite !future_unfold_O; apply fupd_mono.
    - rewrite !future_S.
      iIntros "H"; iMod "H"; iModIntro; iNext.
      iApply IHn; eauto.
  Qed.

 Lemma future_plain {E} P `{Hpl: !Plain P} n :
   (|≫{E}=[n]=> P) ⊢ |={E}=> ▷^n (◇ P).
 Proof.
   rewrite future_unfold; destruct n; iIntros "HP".
   - by iMod "HP"; iModIntro; iApply except_0_intro.
   - iPoseProof (future_plain_base with "HP") as "HP".
     iMod "HP"; iModIntro; simpl in *.
     iNext. iInduction n as [] "IH"; first by eauto.
     simpl. iMod "HP". by iNext; iApply "IH".
 Qed.

 Lemma future_plain'_base {E} Q P `{Hpl: !Plain P} n :
   (Q ⊢ P) → (|≫{E}=[n]=> Q) ⊢ |={E}=> ▷^n (◇ P).
 Proof.
  iIntros (HQP) "HQ". iApply future_plain. iApply future_mono; eauto.
 Qed.

  Lemma future_plain' {E} Q P `{Hpl: !Plain P} n :
   (Q ⊢ P) →
   (|≫{E}=[n]=> Q) ⊢ |={E}=> (|≫{E}=[n]=> Q) ∗ ▷^n (◇ P).
  Proof.
    iIntros (HQP) "HQ".
    iApply fupd_plain_keep_r; iFrame.
    iIntros "HQ". iApply future_plain'_base; eauto.
  Qed.

 Lemma later_n_except_0_future {E} P n :
   ▷^n (◇ P) ⊢ (|≫{E}=[n]=> P).
 Proof.
  rewrite future_eq; induction n; simpl.
  - by iIntros "HP"; iMod "HP"; iModIntro.
  - by iIntros "HP"; iModIntro; iNext; iApply IHn.
 Qed.

 Lemma future_sep {E} P Q n :
  (|≫{E}=[n]=> P) ∗ (|≫{E}=[n]=> Q) ⊢ (|≫{E}=[n]=> P ∗ Q).
 Proof.
  rewrite future_eq; induction n; simpl.
  - iIntros "[HP HQ]"; iMod "HP"; iMod "HQ"; iModIntro; iFrame.
  - iIntros "[HP HQ]";iMod "HP"; iMod "HQ"; iModIntro; iNext; iApply IHn; iFrame.
 Qed.

 Lemma future_cancel_2 {E} P Q Q' m n :
  ((|≫{E}=[m - n]=> P) ∗ Q ⊢ Q') →
  (|≫{E}=[m]=> P) ∗ (|≫{E}=[n]=> Q) ⊢ (|≫{E}=[n]=> Q').
 Proof.
  revert m; induction n => m; simpl.
  - replace (m - 0) with m by lia. intros HA.
    iIntros "[HP HQ]". rewrite !future_unfold_O.
    iMod "HQ"; iModIntro; iApply HA; iFrame.
  - destruct m.
    + replace (0 - S n) with (0 - n) by lia. intros HB; specialize (IHn _ HB).
      iIntros "[HP HQ]"; rewrite !future_S. iMod "HQ"; iModIntro; iNext.
      iApply IHn; iFrame.
    + replace (S m - S n) with (m - n) by omega.
      intros HB; specialize (IHn _ HB).
      iIntros "[HP HQ]"; rewrite !future_S. iMod "HP"; iMod "HQ"; iModIntro; iNext.
      iApply IHn; iFrame.
 Qed.

End future_and_plain.

Section future_properties.
 Context `{!BiFUpd PROP}.

 Implicit Types P Q : PROP.

 Global Instance future_ne k E n :
   Proper (dist n ==> dist n) (@future PROP _ E k).
 Proof.
   rewrite future_eq /future_def; induction k; simpl; first by solve_proper.
   by intros P Q HPQ; apply fupd_ne, (contractive_ne _), IHk.
 Qed.

 Global Instance fupd_proper n E : Proper ((≡) ==> (≡)) (@future PROP _ E n).
 Proof. apply ne_proper, _. Qed.

 Lemma fupd_future_future n E P :
   (|={E}=> (|≫{E}=[n]=> P)) ⊣⊢ (|≫{E}=[n]=> P).
 Proof.
   induction n; rewrite future_unfold; simpl; iSplit;
     iIntros "H"; repeat iMod "H"; eauto.
 Qed.

 Lemma future_fupd_future n E P :
   (|≫{E}=[n]=> |={E}=> P) ⊣⊢ (|≫{E}=[n]=> P).
 Proof.
   induction n.
   - rewrite !future_unfold_O.
     by iSplit; iIntros "H"; repeat iMod "H"; repeat iModIntro.
   - rewrite !future_unfold_S.
     by simpl; do 2 f_equiv.
 Qed.

 Lemma except_0_future n E P : ◇ (|≫{E}=[n]=> P) ≫{E}=[n]=∗ P.
 Proof. rewrite -fupd_future_future; apply except_0_fupd. Qed.

 Lemma future_intro n E P : P ≫{E}=[n]=∗ P.
 Proof.
   induction n; [rewrite future_unfold|rewrite future_S]; simpl;
     iIntros "H"; first by iModIntro.
   by do 2 iModIntro; iApply IHn.
 Qed.

 Lemma bupd_future `{!BiBUpd PROP} `{!BiBUpdFUpd PROP} n E P : (|==> P) ≫{E}=[n]=∗ P.
 Proof.
   induction n; [rewrite future_unfold|rewrite future_S]; simpl;
     iIntros "H". iMod "H"; first done.
   by do 2 iModIntro; iApply IHn.
 Qed.

 Lemma fupd_future n E P : (|={E}=> P) ≫{E}=[n]=∗ P.
 Proof.
   induction n; [rewrite future_unfold|rewrite future_S]; simpl;
     iIntros "H"; first by iMod "H"; auto.
   by do 2 iModIntro; iApply IHn.
 Qed.

 Lemma future_trans n m E P : (|≫{E}=[n]=> |≫{E}=[m]=> P) ≫{E}=[n + m]=∗ P.
 Proof.
   induction n; simpl.
   - by rewrite future_unfold; rewrite fupd_future_future.
   - by rewrite !future_S; rewrite IHn.
 Qed.

 Lemma future_plus n m E P : (|≫{E}=[n]=> |≫{E}=[m]=> P) ⊣⊢ |≫{E}=[n + m]=> P.
 Proof.
   iSplit; first by iApply future_trans.
   iIntros "H".
   iInduction n as [] "IH"; first by iApply future_intro.
   rewrite !future_S.
   iMod "H"; iModIntro. iNext.
   by iApply "IH".
 Qed.

 Lemma future_frame_r n E P Q : (|≫{E}=[n]=> P) ∗ Q ≫{E}=[n]=∗ P ∗ Q.
 Proof.
   induction n.
   - rewrite !future_unfold; apply fupd_frame_r.
   - rewrite !future_S.
     iIntros "[>H1 H2]"; iModIntro; iNext; iApply IHn; by iFrame.
 Qed.

(** * Derived rules *)
Global Instance future_mono' n E : Proper ((⊢) ==> (⊢)) (@future PROP _ E n).
Proof. intros P Q; apply future_mono. Qed.
Global Instance future_flip_mono' n E :
  Proper (flip (⊢) ==> flip (⊢)) (@future PROP _ E n).
Proof. intros P Q; apply future_mono. Qed.

Lemma fupd_except_0 n E P : (|≫{E}=[n]=> ◇ P) ≫{E}=[n]=∗ P.
Proof.
  rewrite {1}(future_intro 0 E P) except_0_future future_trans.
  by replace (n + 0) with n by lia.
Qed.

Lemma future_frame_l n E P Q : P ∗ (|≫{E}=[n]=> Q) ≫{E}=[n]=∗ P ∗ Q.
Proof. rewrite !(comm _ P). apply future_frame_r. Qed.
Lemma future_wand_l n E P Q : (P -∗ Q) ∗ (|≫{E}=[n]=> P) ≫{E}=[n]=∗ Q.
Proof. by rewrite future_frame_l wand_elim_l. Qed.
Lemma future_wand_r n E P Q : (|≫{E}=[n]=> P) ∗ (P -∗ Q) ≫{E}=[n]=∗ Q.
Proof. by rewrite future_frame_r wand_elim_r. Qed.

Lemma wand_future_l n E P Q : P ∗ (|≫{E}=[n]=> P -∗ Q) ≫{E}=[n]=∗ Q.
Proof. by rewrite future_frame_l; apply future_mono; rewrite wand_elim_r. Qed.
Lemma wand_future_r n E P Q : (|≫{E}=[n]=> P -∗ Q) ∗ P ≫{E}=[n]=∗ Q.
Proof. by rewrite future_frame_r; apply future_mono; rewrite wand_elim_l. Qed.

Lemma future_trans_frame n m E P Q :
  ((Q ≫{E}=[n]=∗ emp) ∗ |≫{E}=[m]=> (Q ∗ P)) ≫{E}=[m + n]=∗ P.
Proof.
  rewrite future_frame_l assoc -(comm _ Q) wand_elim_r.
  by rewrite future_frame_r left_id future_trans.
Qed.

Lemma future_mask_frame_r n E Ef P :
  E ## Ef → (|≫{E}=[n]=> P) ≫{E ∪ Ef}=[n]=∗ P.
Proof.
  intros HE. induction n.
  - rewrite !future_unfold. iIntros "H".
    iApply fupd_mask_frame_r'; auto.
    iMod "H"; iModIntro. by iIntros.
  - rewrite !future_S. iIntros "H".
    iApply fupd_mask_frame_r'; auto.
    iMod "H"; iModIntro. iIntros; iNext; by iApply IHn.
Qed.

Lemma future_mask_mono n E1 E2 P : E1 ⊆ E2 → (|≫{E1}=[n]=> P) ≫{E2}=[n]=∗ P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply future_mask_frame_r.
Qed.

Lemma future_big_sepM `{Countable K} {A}
      n E (Φ : K → A → PROP) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, |≫{E}=[n]=> Φ k x) ≫{E}=[n]=∗ [∗ map] k↦x ∈ m, Φ k x.
Proof.
  apply (big_opM_gen_proper (λ P Q, P ≫{E}=[n]=∗ Q)); auto using future_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -future_sep.
Qed.
Lemma future_big_sepS `{Countable A} n E (Φ : A → PROP) X :
  ([∗ set] x ∈ X, |≫{E}=[n]=> Φ x) ≫{E}=[n]=∗ [∗ set] x ∈ X, Φ x.
Proof.
  apply (big_opS_gen_proper (λ P Q, P ≫{E}=[n]=∗ Q)); auto using future_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -future_sep.
Qed.

Lemma embed_future {PROP' : sbi} `{!BiEmbed PROP PROP'} `{!SbiEmbed PROP PROP'}
      `{!BiFUpd PROP'} `{!BiEmbedFUpd PROP PROP'} n E P :
  ⎡|≫{E}=[n]=> P⎤ ⊣⊢@{PROP'} |≫{E}=[n]=> ⎡P⎤.
Proof.
  induction n.
  { rewrite !future_unfold_O; apply embed_fupd. }
  rewrite !future_unfold_S /=.
  rewrite embed_fupd; f_equiv.
  by rewrite embed_later; f_equiv.
Qed.

End future_properties.

Section future_proofmode_classes.
  Context `{!BiFUpd PROP} `{!BiBUpd PROP} `{!BiPlainly PROP}
          `{!BiFUpdPlainly PROP} `{!BiBUpdFUpd PROP}.
  Implicit Types P Q : PROP.

  Global Instance from_pure_future b n E P φ :
    FromPure b P φ → FromPure b (|≫{E}=[n]=> P) φ.
  Proof. rewrite /FromPure. intros <-. apply future_intro. Qed.

  Global Instance from_assumption_future n E p P Q :
    FromAssumption p P (|==> Q) → FromAssumption p P (|≫{E}=[n]=> Q)%I.
  Proof. rewrite /FromAssumption=>->. apply bupd_future. Qed.

  Global Instance into_wand_future n E p q R P Q :
    IntoWand false false P R Q →
    IntoWand p q (|≫{E}=[n]=> P) R (|≫{E}=[n]=> Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite wand_future_l.
  Qed.
  Global Instance into_wand_future_persistent n E p q R P Q :
    IntoWand false q R P Q → IntoWand p q (|≫{E}=[n]=> R) P (|≫{E}=[n]=> Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite future_frame_l wand_elim_r.
  Qed.
  Global Instance into_wand_fupd_args n E p q R P Q :
    IntoWand false false P R Q → IntoWand' p q (|≫{E}=[n]=> P) R (|≫{E}=[n]=> Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l.
    by rewrite !intuitionistically_if_elim future_frame_l wand_elim_r.
  Qed.

  Global Instance from_sep_future n E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|≫{E}=[n]=> P) (|≫{E}=[n]=> Q1) (|≫{E}=[n]=> Q2).
  Proof. rewrite /FromSep=><-. apply future_sep. Qed.

  Global Instance or_split_future n E P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|≫{E}=[n]=> P) (|≫{E}=[n]=> Q1) (|≫{E}=[n]=> Q2).
  Proof. by rewrite /FromOr=><-; apply or_elim; apply future_mono; auto. Qed.

  Global Instance exists_split_future {A} n E P (Φ : A → PROP) :
    FromExist P Φ → FromExist (|≫{E}=[n]=> P) (λ a, |≫{E}=[n]=> Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance frame_future n E p R P Q :
    Frame p R P Q → Frame p R (|≫{E}=[n]=> P) (|≫{E}=[n]=> Q).
  Proof. rewrite /Frame=><-. by rewrite future_frame_l. Qed.

  Global Instance is_except_0_future n E P : IsExcept0 (|≫{E}=[n]=> P).
  Proof. by rewrite /IsExcept0 except_0_future. Qed.

  Global Instance add_modal_embed_fupd_goal {PROP' : sbi} `{!BiEmbed PROP PROP'}
         `{!BiFUpd PROP'} `{!SbiEmbed PROP PROP'} `{!BiEmbedFUpd PROP PROP'}
         n E (P P' : PROP') (Q : PROP) :
    AddModal P P' (|≫{E}=[n]=> ⎡Q⎤)%I → AddModal P P' ⎡|≫{E}=[n]=> Q⎤.
  Proof. by rewrite /AddModal; erewrite !embed_future. Qed.

  Global Instance from_modal_future n E P :
    FromModal modality_id (|≫{E}=[n]=> P) (|≫{E}=[n]=> P) P.
  Proof. rewrite /FromModal. apply future_intro. Qed.

  Global Instance elim_modal_bupd_future `{BiBUpdFUpd PROP} n p E P Q :
    ElimModal True p false (|==> P) P (|≫{E}=[n]=> Q) (|≫{E}=[n]=> Q) | 10.
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim /=
      (bupd_future 0 E) future_frame_r wand_elim_r future_trans.
  Qed.

  Global Instance elim_modal_fupd_future `{BiFUpd PROP} n p E P Q :
    ElimModal True p false (|={E}=> P) P (|≫{E}=[n]=> Q) (|≫{E}=[n]=> Q).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim /=
      fupd_frame_r wand_elim_r fupd_future_future.
  Qed.

  Global Instance elim_modal_embed_future_goal {PROP' : sbi} `{!BiFUpd PROP'}
         `{!BiEmbed PROP PROP'} `{!SbiEmbed PROP PROP'}
         `{!BiEmbedFUpd PROP PROP'}
         n p p' φ E (P P' : PROP') (Q Q' : PROP) :
    ElimModal φ p p' P P' (|≫{E}=[n]=> ⎡Q⎤)%I (|≫{E}=[n]=> ⎡Q'⎤)%I →
    ElimModal φ p p' P P' ⎡|≫{E}=[n]=> Q⎤ ⎡|≫{E}=[n]=> Q'⎤.
  Proof. by rewrite /ElimModal !embed_future. Qed.

  Global Instance elim_modal_embed_future_hyp {PROP' : sbi} `{!BiFUpd PROP'}
         `{!BiEmbed PROP PROP'} `{!SbiEmbed PROP PROP'}
         `{!BiEmbedFUpd PROP PROP'}
         n p p' φ E (P : PROP) (P' Q Q' : PROP') :
    ElimModal φ p p' (|≫{E}=[n]=> ⎡P⎤)%I P' Q Q' →
    ElimModal φ p p' ⎡|≫{E}=[n]=> P⎤ P' Q Q'.
  Proof. by rewrite /ElimModal embed_future. Qed.

  Class CanElimFuture_by (n m : nat) : Prop := can_elim_future_by : n ≤ m.

  Global Instance elim_modal_future_future n m p E P Q :
    CanElimFuture_by m n →
      ElimModal True p false (|≫{E}=[m]=> P) P (|≫{E}=[n]=> Q) ((|≫{E}=[n - m]=> Q)).
  Proof.
    rewrite /ElimModal /CanElimFuture_by.
    rewrite intuitionistically_if_elim.
    revert n; induction m => n; iIntros (Hnm) "_ [HP HQ]".
    - rewrite future_unfold_O. replace (n - 0) with n by lia.
        iMod "HP"; by iApply "HQ".
    - destruct n; simpl; first lia.
      rewrite !future_unfold_S.
      iMod "HP"; iModIntro; iNext.
      iApply IHm; auto with lia.
      iFrame.
  Qed.

End future_proofmode_classes.

Hint Extern 1 (CanElimFuture_by _ _) =>
unfold CanElimFuture_by; abstract omega : typeclass_instances.

Hint Extern 1 (CanElimFuture_by _ _) =>
unfold CanElimFuture_by; abstract lia : typeclass_instances.

Hint Extern 2 (of_envs _ ⊢ _) =>
match goal with |- _ ⊢ |≫{_}=[_]=> _ => iModIntro end : core.
