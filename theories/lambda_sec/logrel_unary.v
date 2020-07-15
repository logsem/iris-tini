From stdpp Require Import list.
From iris.algebra Require Import list.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From IC.if_convergent Require Export IC derived.IC_step_fupd.
From logrel_ifc.lambda_sec Require Export lang rules_unary typing logrel_label.

Reserved Notation "⌊ τ ⌋"  (at level 0, τ at level 70).
Reserved Notation "⌊ τ ⌋ₛ" (at level 0, τ at level 70).
Reserved Notation "⌊ τ ⌋ₑ" (at level 0, τ at level 70).
Reserved Notation "⌊ Γ ⌋*" (at level 0, Γ at level 70).

Section logrel_un.
  Context `{secG_un Σ}.
  Context `{SecurityLattice label}.

  Notation D := (val -d> iPropO Σ).
  Notation lty := (listO D -n> listO labelO -d> D).
  Implicit Types Δ : listO D.
  Implicit Types ρ : listO labelO.
  Implicit Types interp : lty.

  Definition interp_un_expr interp Δ ρ pc e : iProp Σ :=
    ⌜⌊ pc ⌋ₗ ρ ⋢ ζ⌝ → IC@{icd_step_fupd SI} e {{ v, interp Δ ρ v }}.
  Global Instance interp_un_expr_proper n :
    Proper ((dist n) ==> (dist n) ==> (=) ==> (=) ==> (=) ==> dist n) interp_un_expr.
  Proof.
    rewrite /interp_un_expr. intros interp1 interp2.
    repeat intros ?; subst. do 5 f_equiv.
    by apply (ofe_mor_car_ne _ interp1 interp2).
  Qed.

  Program Definition ctx_lookup_un (x : var) : lty :=
    λne Δ, λ ρ, from_option id (const True)%I (Δ !! x).
  Next Obligation.
    intros ? n ????.
    apply (from_option_ne (A := D) _ _ _ _); [done|].
    by apply: list_lookup_ne.
  Qed.

  Program Definition interp_unit : lty := λne Δ, λ ρ w, (⌜w = UnitV⌝)%I.

  Program Definition interp_bool : lty := λne Δ, λ ρ w, (∃ b, ⌜w = BoolV b⌝)%I.

  Program Definition interp_nat : lty := λne Δ, λ ρ w, (∃ n, ⌜w = NatV n⌝)%I.

  Program Definition interp_prod interp1 interp2 : lty := λne Δ, λ ρ w,
    (∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ interp1 Δ ρ w1 ∧ interp2 Δ ρ w2)%I.
  Next Obligation.
    repeat intros ?. do 6 f_equiv; by [apply interp1|apply interp2].
  Qed.

  Program Definition interp_sum interp1 interp2 : lty := λne Δ, λ ρ w,
    ((∃ w1, ⌜w = InjLV w1⌝ ∧ interp1 Δ ρ w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ interp2 Δ ρ w2))%I.
  Next Obligation.
    repeat intros ?. do 4 f_equiv; by [apply interp1|apply interp2].
  Qed.

  Program Definition interp_arrow interp1 interp2 ℓₑ : lty := λne Δ, λ ρ w,
    (<pers> ∀ v, interp1 Δ ρ v → interp_un_expr interp2 Δ ρ ℓₑ (App (# w) (# v)))%I.
  Next Obligation.
    repeat intros ?. do 4 f_equiv; by [apply interp1|f_equiv].
  Qed.

  Program Definition interp_tforall interp ℓₑ : lty := λne Δ, λ ρ w,
    (<pers> ∀ τi : D, ⌜∀ v, Persistent (τi v)⌝ →
       interp_un_expr interp (τi :: Δ) ρ ℓₑ (TApp (# w)))%I.
  Solve Obligations with solve_proper.

  Program Definition interp_lforall interp ℓₑ : lty := λne Δ, λ ρ w,
    (<pers> ∀ ℓ : label, interp_un_expr interp Δ (ℓ :: ρ) ℓₑ (TLApp (# w)))%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref interp τ : lty := λne Δ, λ ρ w,
    (<pers> ∃ (N : namespace) (ι : loc),
        ⌜w = LocV ι⌝ ∧
        let: _ @ ℓ := τ in
        if bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)
        then ∀ (E : coPset), ⌜↑N ⊆ E⌝ →
          |={E, E∖↑N}=> ▷(∃ w, (ι ↦ w ∗ interp Δ ρ w) ∗
                         (▷(ι ↦ w ∗ interp Δ ρ w) ={E∖↑N, E}=∗ True))
        else ∀ (E : coPset), ⌜↑N ⊆ E⌝ →
          |={E, E∖↑N}=> ▷((∃ w, ι ↦ w ∗ interp Δ ρ w) ∗
                       (▷(∃ w', ι ↦ w' ∗ interp Δ ρ w') ={E∖↑N, E}=∗ True)))%I.
  Next Obligation.
    repeat intros ?. destruct τ=> /=. do 7 f_equiv.
    - do 9 f_equiv; [by apply interp|].
      do 2 f_equiv. by apply interp.
    - do 9 f_equiv; [by apply interp|].
      do 2 f_equiv. by apply interp.
  Qed.

  Program Definition interp_exists interp : lty := λne Δ, λ ρ w,
    (<pers> ∃ τi : D, ⌜∀ v, Persistent (τi v)⌝ ∧
       ∃ v, ⌜w = PackV v⌝ ∧ interp (τi :: Δ) ρ v)%I.
  Next Obligation.
    repeat intros ?. do 7 f_equiv. apply interp. by f_equiv.
  Qed.

  Definition interp_un_rec1 interp Δ ρ (τi : D) : D := λne w,
    (<pers> (∃ v, ⌜w = FoldV v⌝ ∧ ▷ interp (τi :: Δ) ρ v))%I.
  Local Arguments interp_un_rec1 /.

  Global Instance interp_un_rec1_contractive
    interp Δ ρ : Contractive (interp_un_rec1 interp Δ ρ).
  Proof.
    rewrite /interp_un_rec1 /=. repeat intros ?.
    do 4 f_equiv. apply bi.later_contractive.
    destruct n as [|n]; [done|].
    apply interp. f_equiv. by apply dist_later_dist.
  Qed.

  Lemma fixpoint_interp_un_rec1_eq interp Δ ρ x :
    fixpoint (interp_un_rec1 interp Δ ρ) x
    ≡ interp_un_rec1 interp Δ ρ (fixpoint (interp_un_rec1 interp Δ ρ)) x.
  Proof. exact: (fixpoint_unfold (interp_un_rec1 interp Δ ρ) x). Qed.

  Program Definition interp_rec interp : lty := λne Δ, λ ρ,
    fixpoint (interp_un_rec1 interp Δ ρ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ ρ.
    apply fixpoint_ne => τi w /=. do 5 f_equiv.
    apply (ofe_mor_ne _ _ interp). by f_equiv.
  Qed.

  Program Fixpoint interp_un (t : type) : lty := tc_opaque
    match t with
    | TUnit => interp_unit
    | TBool => interp_bool
    | TNat => interp_nat
    | TVar x => ctx_lookup_un x
    | TProd τ1 τ2 => interp_prod (interp_un_sec τ1) (interp_un_sec τ2)
    | TSum τ1 τ2 => interp_sum (interp_un_sec τ1) (interp_un_sec τ2)
    | TArrow ℓₑ τ1 τ2 => interp_arrow (interp_un_sec τ1) (interp_un_sec τ2) ℓₑ
    | TForall ℓₑ τ => interp_tforall (interp_un_sec τ) ℓₑ
    | TLForall ℓₑ τ => interp_lforall (interp_un_sec τ) ℓₑ
    | TRef τ => interp_ref (interp_un_sec τ) τ
    | TExist τ => interp_exists (interp_un_sec τ)
    | TRec τ => interp_rec (interp_un_sec τ)
    end%I
  with interp_un_sec (τ : sectype) : lty := tc_opaque
    match τ with
    | TSec _ t => interp_un t
    end.

  Notation "⌊ t ⌋" := (interp_un t).
  Notation "⌊ τ ⌋ₛ" := (interp_un_sec τ).
  Notation "⌊ τ ⌋ₑ" := (interp_un_expr ⌊ τ ⌋ₛ).

  Lemma interp_un_tvar_def Δ ρ x v :
    ⌊ TVar x ⌋ Δ ρ v = from_option id (const True)%I (Δ !! x) v.
  Proof. reflexivity. Qed.
  Lemma interp_un_unit_def Δ ρ v : ⌊ TUnit ⌋ Δ ρ v = (⌜v = UnitV⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_bool_def Δ ρ v : ⌊ TBool ⌋ Δ ρ v = (∃ b, ⌜v = BoolV b⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_nat_def Δ ρ v : ⌊ TNat ⌋ Δ ρ v = (∃ n, ⌜v = NatV n⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_prod_def Δ ρ τ1 τ2 v :
    ⌊ TProd τ1 τ2 ⌋ Δ ρ v =
    (∃ w1 w2, ⌜v = PairV w1 w2⌝ ∧ ⌊ τ1 ⌋ₛ Δ ρ w1 ∧ ⌊ τ2 ⌋ₛ Δ ρ w2)%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_sum_def Δ ρ τ1 τ2 v :
    ⌊ TSum τ1 τ2 ⌋ Δ ρ v =
    ((∃ w1, ⌜v = InjLV w1⌝ ∧ ⌊ τ1 ⌋ₛ Δ ρ w1) ∨ (∃ w2, ⌜v = InjRV w2⌝ ∧ ⌊ τ2 ⌋ₛ Δ ρ w2))%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_arrow_def Δ ρ τ1 τ2 ℓₑ w :
    ⌊ TArrow ℓₑ τ1 τ2 ⌋ Δ ρ w =
    (<pers> ∀ v, ⌊ τ1 ⌋ₛ Δ ρ v → ⌊ τ2 ⌋ₑ Δ ρ ℓₑ (App (# w) (# v)))%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_tforall_def Δ ρ τ ℓₑ w :
    ⌊ TForall ℓₑ τ ⌋ Δ ρ w =
    (<pers> ∀ τi : D, ⌜∀ v, Persistent (τi v)⌝ → ⌊ τ ⌋ₑ (τi :: Δ) ρ ℓₑ (TApp (# w)))%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_tlforall_def Δ ρ τ ℓₑ w :
    ⌊ TLForall ℓₑ τ ⌋ Δ ρ w =
    (<pers> ∀ ℓ : label, ⌊ τ ⌋ₑ Δ (ℓ :: ρ) ℓₑ (TLApp (# w)))%I.
  Proof. reflexivity. Qed.
  Lemma interp_un_exist_def Δ ρ τ w :
    ⌊ TExist τ ⌋ Δ ρ w =
    (<pers> ∃ τi : D, ⌜∀ v, Persistent (τi v)⌝ ∧ ∃ v, ⌜w = PackV v⌝ ∧ ⌊ τ ⌋ₛ (τi :: Δ) ρ v) %I.
  Proof. reflexivity. Qed.
  Lemma interp_un_ref_def Δ ρ τ w :
    ⌊ TRef τ ⌋ Δ ρ w =
    (<pers> ∃ (N : namespace) (ι : loc),
        ⌜w = LocV ι⌝ ∧
        let: _ @ ℓ := τ in
        if bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)
        then ∀ (E : coPset), ⌜↑N ⊆ E⌝ →
          |={E, E∖↑N}=> ▷(∃ w, (ι ↦ w ∗ ⌊ τ ⌋ₛ Δ ρ w) ∗
                         (▷(ι ↦ w ∗ ⌊ τ ⌋ₛ Δ ρ w) ={E∖↑N, E}=∗ True))
        else ∀ (E : coPset), ⌜↑N ⊆ E⌝ →
          |={E, E∖↑N}=> ▷((∃ w, ι ↦ w ∗ ⌊ τ ⌋ₛ Δ ρ w) ∗
                       (▷(∃ w', ι ↦ w' ∗ ⌊ τ ⌋ₛ Δ ρ w') ={E∖↑N, E}=∗ True)))%I.
  Proof. destruct τ; reflexivity. Qed.
  Lemma interp_un_rec_def Δ ρ τ :
    ⌊ TRec τ ⌋ Δ ρ =
    fixpoint (λ (τi : D) w, (<pers> (∃ v, ⌜w = FoldV v⌝ ∧ ▷ ⌊ τ ⌋ₛ (τi :: Δ) ρ v))%I).
  Proof. reflexivity. Qed.
  Lemma interp_un_sec_def Δ ρ t ℓ :
    ⌊ t @ ℓ ⌋ₛ Δ ρ = ⌊ t ⌋ Δ ρ.
  Proof. reflexivity. Qed.

  Global Instance interp_un_proper t :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (⌊ t ⌋).
  Proof.
    repeat intros ?; subst.
    destruct t;
      apply equiv_dist=>?;
      apply (ofe_mor_ne _ _ (interp_un _)), equiv_dist=>//.
  Qed.

  Global Instance interp_un_sec_proper τ :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (⌊ τ ⌋ₛ).
  Proof. destruct τ=>/=. apply _. Qed.

  Class env_Persistent Δ :=
    ctx_persistent : Forall (λ (τi : D), ∀ v, Persistent (τi v)) Δ.
  Global Instance ctx_persistent_nil : env_Persistent [].
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_cons (τi : D) Δ :
    (∀ v, Persistent (τi v)) → env_Persistent Δ → env_Persistent (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_lookup Δ ρ x v :
    env_Persistent Δ → Persistent (ctx_lookup_un x Δ ρ v).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.

  Global Instance interp_rec_persistent interp Δ ρ v :
    Persistent (fixpoint (interp_un_rec1 interp Δ ρ) v).
  Proof.
    rewrite /Persistent fixpoint_interp_un_rec1_eq /=.
      by apply bi.persistently_intro'.
  Qed.

  Fixpoint interp_un_persistent Δ ρ t v :
    env_Persistent Δ →
    Persistent (⌊ t ⌋ Δ ρ v)
  with interp_un_sec_persistent Δ ρ τ v :
    env_Persistent Δ →
    Persistent (⌊ τ ⌋ₛ Δ ρ v).
  Proof.
    - clear interp_un_persistent.
      revert v; induction t=> v HΔ /=; try apply _.
      apply (ctx_persistent_lookup _ [])=> //.
    - clear interp_un_sec_persistent.
      destruct τ=>/=; apply _.
  Qed.

  Global Existing Instance interp_un_persistent.
  Global Existing Instance interp_un_sec_persistent.

  Global Instance interp_un_env_base_persistent Δ ρ Γ vs :
    env_Persistent Δ → TCForall Persistent (zip_with (λ τ, ⌊ τ ⌋ₛ Δ ρ) Γ vs).
  Proof.
    revert vs; induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.

  Definition interp_un_env (Γ : list sectype) Δ ρ (vs : list val) : iProp Σ :=
    (⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⌊ τ ⌋ₛ Δ ρ) Γ vs)%I.

  Notation "⌊ Γ ⌋*" := (interp_un_env Γ).

  Global Instance interp_un_env_persistent Γ Δ ρ vs :
    env_Persistent Δ → Persistent (⌊ Γ ⌋* Δ ρ vs) := _.

  Lemma interp_un_env_nil Δ ρ : ⊢ ⌊ [] ⌋* Δ ρ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_un_env_cons Γ Δ ρ vs τ v :
    ⌊ τ :: Γ ⌋* Δ ρ (v :: vs) ⊣⊢ ⌊ τ ⌋ₛ Δ ρ v ∗ ⌊ Γ ⌋* Δ ρ vs.
  Proof.
    rewrite /interp_un_env /= (assoc _ (⌊ _ ⌋ₛ _ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
      by apply bi.sep_proper; [apply bi.pure_proper; lia|].
  Qed.

  Lemma interp_un_env_length Γ Δ ρ vs : ⌊ Γ ⌋* Δ ρ vs ⊢ ⌜length Γ = length vs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_un_env_Some_l Γ Δ ρ vs x τ :
    ⌜Γ !! x = Some τ⌝ ∧ ⌊ Γ ⌋* Δ ρ vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⌊ τ ⌋ₛ Δ ρ v.
  Proof.
    iIntros "(% & %Hlen & HΓ)".
    destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
   Qed.

  Lemma interp_un_label_weaken t ρ1 ξ ρ2 Δ :
    ⌊ t.|[upn (length ρ1) (ren (+ length ξ))] ⌋ Δ (ρ1 ++ ξ ++ ρ2)
    ≡ ⌊ t ⌋ Δ (ρ1 ++ ρ2)
  with interp_un_sec_label_weaken τ ρ1 ξ ρ2 Δ :
    ⌊ hsubst (inner := label_term)
      (upn (length ρ1) (ren (+ length ξ))) τ ⌋ₛ Δ (ρ1 ++ ξ ++ ρ2)
    ≡ ⌊ τ ⌋ₛ Δ (ρ1 ++ ρ2).
  Proof.
    - destruct t=> /=; [done|done|done|done|..].
      + destruct τ=> w /=. properness; auto. rewrite interp_label_weaken //. f_equiv.
        * properness; auto; by apply interp_un_label_weaken.
        * properness; auto; by apply interp_un_label_weaken.
      + rewrite /interp_un_expr => w.
        properness; try by apply interp_un_sec_label_weaken.
        rewrite interp_label_weaken //.
      + move=> w; properness; auto; by apply interp_un_sec_label_weaken.
      + move=> w; properness; auto; by apply interp_un_sec_label_weaken.
      + rewrite /interp_un_expr => w.
        properness; auto; [|by apply interp_un_sec_label_weaken].
        rewrite interp_label_weaken //.
      + rewrite /interp_un_expr => w. properness; auto.
        * asimpl. rewrite (interp_label_weaken _ (_ :: _)) //.
        * by apply (interp_un_sec_label_weaken _ (_ :: _)).
      + move=>w; properness; auto; by apply interp_un_sec_label_weaken.
      + properness; auto. apply interp_un_sec_label_weaken.
    - by destruct τ => /=.
  Qed.

  Fixpoint interp_un_type_weaken t Δ1 Π Δ2 n m ρ {struct t} :
    n = length Δ1 →
    m = length Π →
    ⌊ t.[upn n (ren (+m))] ⌋ (Δ1 ++ Π ++ Δ2) ρ ≡ ⌊ t ⌋ (Δ1 ++ Δ2) ρ
  with interp_un_sec_type_weaken τ Δ1 Π Δ2 n m ρ {struct τ} :
    n = length Δ1 →
    m = length Π →
    ⌊ τ.|[upn n (ren (+m))] ⌋ₛ (Δ1 ++ Π ++ Δ2) ρ ≡ ⌊ τ ⌋ₛ (Δ1 ++ Δ2) ρ.
  Proof.
    - intros -> ->. destruct t => /=; [done|done|done|..].
      + asimpl. rewrite iter_up; destruct lt_dec as [Hl | Hl] => /=.
        { by rewrite !lookup_app_l. }
        rewrite !(lookup_app_r (A := D)); [|lia ..].
        do 2 f_equiv. lia.
      + destruct τ => w /=. properness; auto. f_equiv.
        * properness; auto; by apply interp_un_type_weaken.
        * properness; auto; by apply interp_un_type_weaken.
      + rewrite /interp_un_expr => ? /=.
        properness; auto; by apply interp_un_sec_type_weaken.
      + intros ?. properness; auto; by apply interp_un_sec_type_weaken.
      + intros ?. properness; auto; by apply interp_un_sec_type_weaken.
      + rewrite /interp_un_expr => ? /=. properness; auto. asimpl.
        by apply (interp_un_sec_type_weaken _ (_ :: _)).
      + rewrite /interp_un_expr => ? /=. properness; auto.
        rewrite -up_hcomp_n_internal; last apply up_hcomp_dist.
        by apply (interp_un_sec_type_weaken).
      + intros ?. properness; auto. asimpl.
        by apply (interp_un_sec_type_weaken _ (_ :: _)).
      + properness; auto. asimpl.
        by apply (interp_un_sec_type_weaken _ (_ :: _)).
    - destruct τ => /=. apply interp_un_type_weaken.
  Qed.

  Lemma interp_un_label_ren t Δ ℓ ρ :
    ⌊ t.|[ren (+1)] ⌋ Δ (ℓ :: ρ) ≡ ⌊ t ⌋ Δ ρ.
  Proof. apply (interp_un_label_weaken _ [] [_]). Qed.

  Fixpoint interp_un_label_subst_up t ρ1 ρ2 Δ l {struct t} :
    ⌊ t.|[upn (length ρ1) (l .: ids)] ⌋ Δ (ρ1 ++ ρ2)
    ≡  ⌊ t ⌋ Δ (ρ1 ++ ⌊ l ⌋ₗ ρ2 :: ρ2)
  with interp_un_sec_label_subst_up τ ρ1 ρ2 Δ l {struct τ} :
    ⌊ hsubst (inner := label_term)
      (upn (length ρ1) (l .: ids)) τ ⌋ₛ Δ (ρ1 ++ ρ2)
    ≡ ⌊ τ ⌋ₛ Δ (ρ1 ++ ⌊ l ⌋ₗ ρ2 :: ρ2).
  Proof.
    - destruct t=> /=; [done|done|done|done|..].
      + destruct τ=> w /=. properness; auto.
        rewrite interp_label_subst_up. f_equiv.
        * properness; auto; by apply interp_un_label_subst_up.
        * properness; auto; by apply interp_un_label_subst_up.
      + rewrite /interp_un_expr => w.
        properness; try by apply interp_un_sec_label_subst_up.
        by rewrite interp_label_subst_up.
      + move=> w; properness; auto; apply interp_un_sec_label_subst_up.
      + move=> w; properness; auto; apply interp_un_sec_label_subst_up.
      + rewrite /interp_un_expr=> ? /=.
        properness; auto; [|by apply interp_un_sec_label_subst_up].
        by rewrite interp_label_subst_up.
      + rewrite /interp_un_expr=> ? /=.
        properness; [|by apply (interp_un_sec_label_subst_up _  (_ :: _))].
        by rewrite (interp_label_subst_up _ _ (_ :: _)).
      + move=> w; properness; auto. apply interp_un_sec_label_subst_up.
      + properness; auto. apply interp_un_sec_label_subst_up.
    - destruct τ => /=. by apply interp_un_label_subst_up.
  Qed.

  Lemma interp_un_label_subst1 t Δ ℓ ρ :
    ⌊ hsubst (inner := label_term) (ℓ .: ids) t ⌋ Δ ρ
    ≡  ⌊ t ⌋ Δ (⌊ ℓ ⌋ₗ ρ :: ρ).
  Proof. apply (interp_un_label_subst_up _ []). Qed.

  Lemma interp_un_type_subst_up t Δ1 Δ2 n ρ t' :
    n = (length Δ1) →
    ⌊ t ⌋ (Δ1 ++ ⌊ t' ⌋ Δ2 ρ :: Δ2) ρ
    ≡ ⌊ t.[upn n (t' .: ids)] ⌋ (Δ1 ++ Δ2) ρ
  with interp_un_sec_type_subst_up τ Δ1 Δ2 n ρ t' :
    n = (length Δ1) →
    ⌊ τ ⌋ₛ (Δ1 ++ ⌊ t' ⌋ Δ2 ρ :: Δ2) ρ
    ≡ ⌊ τ.|[upn n (t' .: ids)] ⌋ₛ (Δ1 ++ Δ2) ρ.
  Proof.
    - intros ->. destruct t=>/=; [done|done|done|..].
      + asimpl. rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
        { by rewrite !lookup_app_l. }
        asimpl. rewrite (lookup_app_r (A := D)); [|lia ..].
        case EQ: (x - length Δ1) => [|m]; simpl.
        { rewrite (interp_un_type_weaken _ [] Δ1 _ 0) => //. }
        rewrite (lookup_app_r (A := D)); [|lia].
        do 2 f_equiv. lia.
      + destruct τ=> ? /=. properness; auto. f_equiv.
        * properness; auto; apply interp_un_type_subst_up=>//.
        * properness; auto; apply interp_un_type_subst_up=>//.
      + rewrite /interp_un_expr => ? /=.
        properness; auto; apply interp_un_sec_type_subst_up=>//.
      + intros ?; properness; auto; apply interp_un_sec_type_subst_up=>//.
      + intros ?; properness; auto; apply interp_un_sec_type_subst_up=>//.
      + rewrite /interp_un_expr => ? /=. properness; auto.
        asimpl. apply (interp_un_sec_type_subst_up _ (_ :: _))=>//.
      + rewrite /interp_un_expr => ? /=. properness; auto.
        rewrite -interp_un_label_ren upn_hsubst_ren.
        apply interp_un_sec_type_subst_up=>//.
      + intros ?; properness; auto. asimpl.
        apply (interp_un_sec_type_subst_up _ (_ :: _))=>//.
      + properness; auto. asimpl.
        apply (interp_un_sec_type_subst_up _ (_ :: _))=>//.
    - intros ->. destruct τ. by apply interp_un_type_subst_up.
  Qed.

  Lemma interp_un_env_ren Δ ρ Γ vs τi :
    ⌊ hsubst_sectype (ren (+1)) <$> Γ ⌋* (τi :: Δ) ρ vs ⊣⊢ ⌊ Γ ⌋* Δ ρ vs.
  Proof.
    apply bi.sep_proper; [apply bi.pure_proper; by rewrite fmap_length|].
    revert Δ vs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply bi.sep_proper; auto. by apply (interp_un_sec_type_weaken _ [] [_] _ 0).
  Qed.

  Lemma interp_un_env_label_ren Δ ρ Γ vs ℓ :
    ⌊ hsubst_label_sectype (ren (+1)) <$> Γ ⌋* Δ (ℓ :: ρ) vs ⊣⊢ ⌊ Γ ⌋* Δ ρ vs.
  Proof.
    apply bi.sep_proper; [apply bi.pure_proper; by rewrite fmap_length|].
    revert ρ vs ℓ; induction Γ=> ρ [|v vs] ℓ; csimpl; auto.
    apply bi.sep_proper; auto. by apply (interp_un_sec_label_weaken _ [] [_]).
  Qed.

End logrel_un.

Notation "⌊ t ⌋" := (interp_un t).
Notation "⌊ τ ⌋ₛ" := (interp_un_sec τ).
Notation "⌊ τ ⌋ₑ" := (interp_un_expr ⌊ τ ⌋ₛ).
Notation "⌊ Γ ⌋*" := (interp_un_env Γ).

Typeclasses Opaque interp_un.
Typeclasses Opaque interp_un_sec.
Typeclasses Opaque interp_un_env.

Global Opaque interp_un.
Global Opaque interp_un_sec.
Global Opaque interp_un_env.
