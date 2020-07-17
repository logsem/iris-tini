From iris.algebra Require Import list.
From iris.bi Require Import big_op.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Import lifting.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From logrel_ifc.lambda_sec Require Export lang typing logrel_unary rules_binary lattice.

Reserved Notation "⟦ τ ⟧ₛ" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).

Section logrel.
  Context `{!secG Σ}.
  Context `{SecurityLattice label}.

  Notation D := (val -d> iPropO Σ).
  Notation P := (val * val -d> iPropO Σ).
  Notation T := (prodO P (prodO D D)).
  Notation lty := (listO T -n> listO labelO -d> P).

  Implicit Types Θ : listO T.
  Implicit Types ρ : listO labelO.
  Implicit Types interp : lty.

  Definition interp_expr interp Θ ρ (ee : expr * expr) : iProp Σ :=
    (IC@{ic_binary, ee.2} ee.1 {{ v ; _ | w ; m , interp Θ ρ (v, w) }})%I.
  Global Instance interp_expr_proper n :
    Proper ((dist n) ==> (dist n) ==> (=) ==> (=) ==> dist n) interp_expr.
  Proof.
    rewrite /interp_expr. intros interp1 interp2.
    repeat intros ?; subst. do 4 f_equiv. simpl.
    by apply (ofe_mor_car_ne _ interp1 interp2).
  Qed.

  Notation proj_bin Θ := (Θ.*1 : listO P).
  Notation projl Θ := (Θ.*2.*1 : listO D).
  Notation projr Θ := (Θ.*2.*2 : listO D).

  Definition interp_ref_inv ll interp Θ ρ :=
    (∃ w w', ll.1 ↦ₗ w ∗ ll.2 ↦ᵣ w' ∗ interp Θ ρ (w, w'))%I.

  Program Definition ctx_lookup (x : var) : lty :=
    λne Θ, λ ρ, from_option id (const True)%I ((proj_bin Θ) !! x).
  Next Obligation.
    intros ? n ????.
    apply (from_option_ne (A := P) _ _ _ _); [done|].
    apply: list_lookup_ne.
    by f_equiv.
  Qed.

  Program Definition interp_unit : lty :=
    λne Θ, λ ρ vv, (⌜vv.1 = UnitV⌝ ∧ ⌜vv.2 = UnitV⌝)%I.

  Program Definition interp_bool : lty :=
    λne Θ, λ ρ vv, (∃ b1 b2, ⌜vv.1 = BoolV b1⌝ ∧ ⌜vv.2 = BoolV b2⌝ ∧ ⌜b1 = b2⌝)%I.

  Program Definition interp_nat : lty :=
    λne Θ, λ ρ vv, (∃ n1 n2, ⌜vv.1 = NatV n1⌝ ∧ ⌜vv.2 = NatV n2⌝ ∧ ⌜n1 = n2⌝)%I.

  Program Definition interp_prod interp1 interp2 : lty := λne Θ, λ ρ vv,
    (∃ v1 v2 w1 w2, ⌜vv.1 = PairV v1 v2⌝ ∧ ⌜vv.2 = PairV w1 w2⌝ ∧
                    interp1 Θ ρ (v1, w1) ∧ interp2 Θ ρ (v2, w2))%I.
  Next Obligation.
    repeat intros ?. do 11 f_equiv; by [apply interp1|apply interp2].
  Qed.

  Program Definition interp_sum interp1 interp2 : lty := λne Θ, λ ρ vv,
    (∃ v' w', (⌜vv = (InjLV v', InjLV w')⌝ ∧ interp1 Θ ρ (v', w')) ∨
              (⌜vv = (InjRV v', InjRV w')⌝ ∧ interp2 Θ ρ (v', w')))%I.
  Next Obligation.
    repeat intros ?. do 6 f_equiv; by [apply interp1|apply interp2].
  Qed.

  Program Definition interp_arrow interp1 interp2 τ1 τ2 ℓₑ : lty := λne Θ, λ ρ vv,
    (<pers>
     (∀ ww,
         (interp1 Θ ρ ww →
          interp_expr interp2 Θ ρ (App (# vv.1) (# ww.1), App (# vv.2) (# ww.2))))
     ∧ ⌊ TArrow ℓₑ τ1 τ2 ₗ⌋ (projl Θ) ρ vv.1
     ∧ ⌊ TArrow ℓₑ τ1 τ2 ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Next Obligation.
    repeat intros ?. do 2 f_equiv.
    - do 3 f_equiv; by [apply interp1|f_equiv].
    - apply (ofe_mor_car_ne _ _ (interp_un _)); [done|].
      by do 2 f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un _)); [done|].
      by do 2 f_equiv.
  Qed.

  Program Definition interp_ref interp : lty := λne Θ, λ ρ vv,
     (∃ ll, ⌜vv = (LocV (ll.1), LocV (ll.2))⌝ ∧
            inv (nroot .@ ll) (interp_ref_inv ll interp Θ ρ))%I.
  Next Obligation.
    repeat intros ?. rewrite /interp_ref_inv.
    do 10 f_equiv. by apply interp.
  Qed.

  Program Definition interp_tforall interp τ ℓₑ : lty := λne Θ, λ ρ vv,
    (<pers>
     (∀ (τR : P) (τi1 τi2 : D),
         ⌜∀ vv, Persistent (τR vv)⌝ →
         ⌜∀ v, Persistent (τi1 v)⌝ → ⌜∀ v, Persistent (τi2 v)⌝ →
         (<pers> (∀ vv, τR vv → τi1 vv.1 ∧ τi2 vv.2)) →
         (interp_expr interp ((τR, (τi1, τi2)) :: Θ) ρ (TApp (# vv.1), TApp (# vv.2))))
     ∧ ⌊ TForall ℓₑ τ ₗ⌋ (projl Θ) ρ vv.1
     ∧ ⌊ TForall ℓₑ τ ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Next Obligation.
    repeat intros ?. do 2 f_equiv.
    - rewrite /interp_expr. do 14 f_equiv. apply interp. by f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un _ )); [done|].
      by do 2 f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un _ )); [done|].
      by do 2 f_equiv.
    Qed.

  Program Definition interp_tlforall interp τ ℓₑ : lty := λne Θ, λ ρ vv,
    (<pers>
     (∀ ℓ, interp_expr interp Θ (ℓ :: ρ) (TLApp (# vv.1), TLApp (# vv.2)))
     ∧ ⌊ TLForall ℓₑ τ ₗ⌋ (projl Θ) ρ vv.1
     ∧ ⌊ TLForall ℓₑ τ ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Next Obligation.
    repeat intros ?. do 2 f_equiv.
    - rewrite /interp_expr. do 6 f_equiv. by apply interp.
    - apply (ofe_mor_car_ne _ _ (interp_un _ )); [done|].
      by do 2 f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un _ )); [done|].
      by do 2 f_equiv.
  Qed.

  Program Definition interp_exists interp : lty := λne Θ, λ ρ vv,
    (<pers>
     (∃ (τR : P) (τi1 τi2 : D),
       ⌜∀ vv, Persistent (τR vv)⌝ ∧
       ⌜∀ v, Persistent (τi1 v)⌝ ∧ ⌜∀ v, Persistent (τi2 v)⌝ ∧
       (<pers> (∀ vv, τR vv → τi1 vv.1 ∧ τi2 vv.2)) ∧
       ∃ ww, ⌜vv.1 = PackV ww.1⌝ ∧ ⌜vv.2 = PackV ww.2⌝ ∧ interp ((τR, (τi1, τi2)) :: Θ) ρ ww))%I.
  Next Obligation.
    repeat intros ?. do 15 f_equiv. apply interp. by f_equiv.
  Qed.

  Program Definition interp_rec1 interp τ Θ ρ (τi : P) : P := λne vv,
    (<pers>
     (∃ ww, ⌜vv = (FoldV ww.1, FoldV ww.2)⌝
            ∧ ▷ interp ((τi, (⌊ TRec τ ₗ⌋ (projl Θ) ρ, ⌊ TRec τ ᵣ⌋ (projr Θ) ρ)) :: Θ) ρ ww))%I.
  Next Obligation.
    repeat intros ?.
    move: H => /discrete_iff /leibniz_equiv_iff ->.
    solve_proper.
  Qed.
  Local Arguments interp_rec1 /.

  Global Instance interp_rec1_contractive interp τ Θ ρ :
    Contractive (interp_rec1 interp τ Θ ρ).
  Proof.
    rewrite /interp_rec1. cbn. repeat intros ?.
    do 4 f_equiv. f_contractive.
    apply interp. do 2 f_equiv. by apply dist_later_dist.
  Qed.

  Lemma fixpoint_interp_rec1_eq interp τ Θ ρ x :
    fixpoint (interp_rec1 interp τ Θ ρ) x
    ≡ interp_rec1 interp τ Θ ρ (fixpoint (interp_rec1 interp τ Θ ρ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp _ _ _) _). Qed.

  Program Definition interp_rec interp τ : lty := λne Θ, λ ρ,
    fixpoint (interp_rec1 interp τ Θ ρ).
  Next Obligation.
    intros interp τ n Θ1 Θ2 HΘ ρ.
    apply fixpoint_ne => τi w. cbn. do 5 f_equiv.
    apply (ofe_mor_ne _ _ interp). f_equiv; [|done]. do 2 f_equiv.
    + apply (ofe_mor_ne _ _ (interp_un _)). by do 2 f_equiv.
    + apply (ofe_mor_ne _ _ (interp_un _)). by do 2 f_equiv.
  Qed.

  Program Definition interp_sec' interp τ : lty := λne Θ, λ ρ vv,
    let: _ @ ℓ := τ in
    (if bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)
     then interp Θ ρ vv
     else ⌊ τ ₗ⌋ₛ (projl Θ) ρ vv.1 ∧ ⌊ τ ᵣ⌋ₛ (projr Θ) ρ vv.2)%I.
  Next Obligation.
    repeat intros ?. destruct τ=>/=.
    f_equiv; [by apply interp|]. f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un_sec _)); [done|].
      by do 2 f_equiv.
    - apply (ofe_mor_car_ne _ _ (interp_un_sec _)); [done|].
      by do 2 f_equiv.
  Qed.

  Program Fixpoint interp (t : type) : lty := tc_opaque
    match t with
    | TUnit => interp_unit
    | TBool => interp_bool
    | TNat => interp_nat
    | TVar x => ctx_lookup x
    | TProd τ1 τ2 => interp_prod (interp_sec τ1) (interp_sec τ2)
    | TSum τ1 τ2 => interp_sum (interp_sec τ1) (interp_sec τ2)
    | TArrow ℓₑ τ1 τ2 => interp_arrow (interp_sec τ1) (interp_sec τ2) τ1 τ2 ℓₑ
    | TForall ℓₑ τ => interp_tforall (interp_sec τ) τ ℓₑ
    | TLForall ℓₑ τ => interp_tlforall (interp_sec τ) τ ℓₑ
    | TRef τ => interp_ref (interp_sec τ)
    | TExist τ => interp_exists (interp_sec τ)
    | TRec τ => interp_rec (interp_sec τ) τ
  end%I
  with interp_sec (τ : sectype) : lty :=
    let: t @ _ := τ in tc_opaque (interp_sec' (interp t) τ).

  Notation "⟦ τ ⟧ₛ" := (interp_sec τ).
  Notation "⟦ t ⟧"  := (interp t).
  Notation "⟦ τ ⟧ₑ" := (interp_expr ⟦ τ ⟧ₛ).

  Lemma interp_tvar_def Θ ρ x :
    ⟦ TVar x ⟧ Θ ρ = from_option id (const True)%I ((proj_bin Θ) !! x).
  Proof. reflexivity. Qed.
  Lemma interp_unit_def Θ ρ vv :
    ⟦ TUnit ⟧ Θ ρ vv = (⌜vv.1 = UnitV⌝ ∧ ⌜vv.2 = UnitV⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_bool_def Θ ρ vv :
    ⟦ TBool ⟧ Θ ρ vv = (∃ b1 b2, ⌜vv.1 = BoolV b1⌝ ∧ ⌜vv.2 = BoolV b2⌝ ∧ ⌜b1 = b2⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_nat_def Θ ρ vv :
    ⟦ TNat ⟧ Θ ρ vv = (∃ n1 n2, ⌜vv.1 = NatV n1⌝ ∧ ⌜vv.2 = NatV n2⌝ ∧ ⌜n1 = n2⌝)%I.
  Proof. reflexivity. Qed.
  Lemma interp_prod_def Θ ρ vv τ1 τ2 :
    ⟦ TProd τ1 τ2 ⟧ Θ ρ vv =
      (∃ v1 v2 w1 w2, ⌜vv.1 = PairV v1 v2⌝ ∧ ⌜vv.2 = PairV w1 w2⌝ ∧
                      ⟦ τ1 ⟧ₛ Θ ρ (v1, w1) ∧ ⟦ τ2 ⟧ₛ Θ ρ (v2, w2))%I.
  Proof. reflexivity. Qed.
  Lemma interp_sum_def Θ ρ vv τ1 τ2 :
    ⟦ TSum τ1 τ2 ⟧ Θ ρ vv =
      (∃ v' w', (⌜vv = (InjLV v', InjLV w')⌝ ∧ ⟦ τ1 ⟧ₛ Θ ρ (v', w')) ∨
                (⌜vv = (InjRV v', InjRV w')⌝ ∧ ⟦ τ2 ⟧ₛ Θ ρ (v', w')))%I.
  Proof. reflexivity. Qed.
  Lemma interp_arrow_def Θ ρ vv τ1 τ2 ℓₑ :
    ⟦ TArrow ℓₑ τ1 τ2 ⟧ Θ ρ vv =
      (<pers> (∀ ww,
         (⟦ τ1 ⟧ₛ Θ ρ ww →
          ⟦ τ2 ⟧ₑ Θ ρ (App (# vv.1) (# ww.1), App (# vv.2) (# ww.2))))
      ∧ ⌊ TArrow ℓₑ τ1 τ2 ₗ⌋ (projl Θ) ρ vv.1
      ∧ ⌊ TArrow ℓₑ τ1 τ2 ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Proof. reflexivity. Qed.
  Lemma interp_tforall_def Θ ρ vv τ ℓₑ :
    ⟦ TForall ℓₑ τ ⟧ Θ ρ vv =
      (<pers> (∀ (τR : P) (τi1 τi2 : D),
         ⌜∀ vv, Persistent (τR vv)⌝ →
         ⌜∀ v, Persistent (τi1 v)⌝ → ⌜∀ v, Persistent (τi2 v)⌝ →
         (<pers> (∀ vv, τR vv → τi1 vv.1 ∧ τi2 vv.2)) →
         (⟦ τ ⟧ₑ ((τR, (τi1, τi2)) :: Θ) ρ (TApp (# vv.1), TApp (# vv.2))))
      ∧ ⌊ TForall ℓₑ τ ₗ⌋ (projl Θ) ρ vv.1
      ∧ ⌊ TForall ℓₑ τ ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Proof. reflexivity. Qed.
  Lemma interp_tlforall_def Θ ρ vv τ ℓₑ :
    ⟦ TLForall ℓₑ τ ⟧ Θ ρ vv =
      (<pers>
         (∀ ℓ, ⟦ τ ⟧ₑ Θ (ℓ :: ρ) (TLApp (# vv.1), TLApp (# vv.2)))
      ∧ ⌊ TLForall ℓₑ τ ₗ⌋ (projl Θ) ρ vv.1
      ∧ ⌊ TLForall ℓₑ τ ᵣ⌋ (projr Θ) ρ vv.2)%I.
  Proof. reflexivity. Qed.
  Lemma interp_exist_def Θ ρ vv τ :
    ⟦ TExist τ ⟧ Θ ρ vv =
      (<pers>
        (∃ (τR : P) (τi1 τi2 : D),
          ⌜∀ vv, Persistent (τR vv)⌝ ∧
          ⌜∀ v, Persistent (τi1 v)⌝ ∧ ⌜∀ v, Persistent (τi2 v)⌝ ∧
          (<pers> (∀ vv, τR vv → τi1 vv.1 ∧ τi2 vv.2)) ∧
            ∃ ww, ⌜vv.1 = PackV ww.1⌝ ∧ ⌜vv.2 = PackV ww.2⌝ ∧ ⟦ τ ⟧ₛ ((τR, (τi1, τi2)) :: Θ) ρ ww))%I.
  Proof. reflexivity. Qed.
  Lemma interp_rec_def Θ ρ τ :
    ⟦ TRec τ ⟧ Θ ρ =
      fixpoint (λ (τi : P) vv,
        (<pers>
           (∃ ww, ⌜vv = (FoldV ww.1, FoldV ww.2)⌝
             ∧ ▷ ⟦ τ ⟧ₛ ((τi, (⌊ TRec τ ₗ⌋ (projl Θ) ρ, ⌊ TRec τ ᵣ⌋ (projr Θ) ρ)) :: Θ) ρ ww)))%I.
  Proof. reflexivity. Qed.
  Lemma interp_ref_def Θ ρ τ vv :
    ⟦ TRef τ ⟧ Θ ρ vv =
      (∃ ll, ⌜vv = (LocV (ll.1), LocV (ll.2))⌝ ∧
             inv (nroot .@ ll) (interp_ref_inv ll (⟦ τ ⟧ₛ) Θ ρ))%I.
  Proof. reflexivity. Qed.
  Lemma interp_sec_def Θ ρ τ vv :
    ⟦ τ ⟧ₛ Θ ρ vv =
      let: t @ ℓ := τ in
      (if bool_decide (⌊ ℓ ⌋ₗ ρ ⊑ ζ)
       then ⟦ t ⟧ Θ ρ vv
       else ⌊ τ ₗ⌋ₛ (projl Θ) ρ vv.1 ∧ ⌊ τ ᵣ⌋ₛ (projr Θ) ρ vv.2)%I.
  Proof. destruct τ; reflexivity. Qed.

  Global Instance interp_proper t :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (⟦ t ⟧).
  Proof.
    repeat intros ?; subst.
    destruct t;
      apply equiv_dist=>?;
      apply (ofe_mor_ne _ _ (interp _)), equiv_dist=>//.
  Qed.

  Global Instance interp_sec_proper τ :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (⟦ τ ⟧ₛ).
  Proof.
    repeat intros ?; subst. destruct τ. rewrite !interp_sec_def /=.
    f_equiv; [by apply interp_proper|].
    f_equiv; apply interp_un_sec_proper => //; by do 2 f_equiv.
  Qed.

  Class env_Persistent_bin (Π : listO P) :=
    ctx_persistent' : Forall (λ (τR : P), ∀ vv, Persistent (τR vv)) Π.
  Global Instance ctx_persistent_bin_nil : env_Persistent_bin [].
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_bin_cons (τi : P) (Π : listO P) :
    (∀ vv, Persistent (τi vv)) → env_Persistent_bin Π → env_Persistent_bin (τi :: Π).
  Proof. by constructor. Qed.

  Global Instance ctx_persistent_bin_lookup ρ x v :
    env_Persistent_bin (proj_bin Θ) → Persistent (ctx_lookup x Θ ρ v).
  Proof.
    intros HΘ; revert x; induction HΘ=>-[|?] /=; try apply _.
    - move=> /(Forall_cons_1 _ _) [? ?] //.
    - move=> /(Forall_cons_1 _ _) [? ?]. apply IHHΘ => //.
  Qed.

  Class envs_Persistent (Θ : listO T) :=
    ctxs_Persistent :
      env_Persistent_bin (proj_bin Θ)
      ∧ env_Persistent (projl Θ)
      ∧ env_Persistent (projr Θ).

  Global Instance envs_Persistent_nil :
    envs_Persistent [].
  Proof. repeat split; apply _. Qed.
  Global Instance envs_Persistent_cons Θ (τR : P) (τi1 τi2 : D) :
    (∀ vv, Persistent (τR vv)) →
    (∀ v, Persistent (τi1 v)) →
    (∀ v, Persistent (τi2 v)) →
    envs_Persistent Θ →
    envs_Persistent ((τR, (τi1, τi2)) :: Θ).
  Proof.
    intros ??? (?&?&?). constructor; first apply _.
    split; apply _.
  Qed.
  Global Instance envs_Persistent_lookup Θ ρ x v :
    envs_Persistent Θ → Persistent (ctx_lookup x Θ ρ v).
  Proof. move=> []?; apply _. Qed.

  Global Instance envs_Persistent_env_left Θ :
     envs_Persistent Θ → env_Persistent (projl Θ).
  Proof. by intros (?&?&?). Qed.
  Global Instance envs_Persistent_env_right Θ :
     envs_Persistent Θ → env_Persistent (projr Θ).
  Proof. by intros (?&?&?). Qed.

  Global Instance interp_rec_persistent interp Θ ρ τ v :
    Persistent (interp_rec interp τ Θ ρ v).
  Proof.
    rewrite /Persistent /interp_rec. cbn.
    rewrite fixpoint_interp_rec1_eq. auto.
  Qed.

  Definition env_coherent (Θ : listO T) : iProp Σ :=
    ([∗ list] _ ↦ x ∈ Θ,
     <pers> ∀ vv, (x.1 : P) vv → (x.2.1 : D) vv.1 ∧ (x.2.2 : D) vv.2)%I.

  Fixpoint interp_persistent t Θ ρ vv :
    envs_Persistent Θ →
    Persistent (⟦ t ⟧ Θ ρ vv)
  with interp_sec_persistent τ Θ ρ vv :
    envs_Persistent Θ →
    Persistent (⟦ τ ⟧ₛ Θ ρ vv).
  Proof.
    - clear interp_persistent.
      revert vv; induction t=> v HΘ /=; try apply _.
      apply (envs_Persistent_lookup _ []) => //.
    - destruct τ. rewrite interp_sec_def.
      case_bool_decide; apply _.
  Qed.

  Global Existing Instance interp_persistent.
  Global Existing Instance interp_sec_persistent.

  Definition interp_env (Γ : list sectype) Θ ρ (vvs : list (val * val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ₛ Θ ρ) Γ vvs)%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Lemma interp_env_nil Θ ρ : ⊢ ⟦ [] ⟧* Θ ρ [].
  Proof. iSplit; simpl; auto. Qed.

  Lemma interp_env_cons Γ Θ ρ vs τ v :
    ⟦ τ :: Γ ⟧* Θ ρ (v :: vs) ⊣⊢ ⟦ τ ⟧ₛ Θ ρ v ∗ ⟦ Γ ⟧* Θ ρ vs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ₛ _ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
      by apply bi.sep_proper; [apply bi.pure_proper; lia|].
  Qed.

  Lemma interp_env_Some_l Γ Θ ρ vvs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Θ ρ vvs -∗ ∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ₛ Θ ρ vv.
  Proof.
    iIntros (?) "[%Hlen HΓ]".
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Global Instance interp_env_persistent Γ Θ vs :
    envs_Persistent Θ →
    Persistent (⟦ Γ ⟧* Θ ρ vs).
  Proof.
    revert vs; induction Γ; intros vs; rewrite /interp_env; first apply _.
    rewrite /Persistent /=; destruct vs; simpl; first by iIntros "% % [% ?]".
    iIntros (??) "[% [#Ha HΓ]]".
    repeat iSplit; eauto.
    rewrite /Persistent /interp_env in IHΓ.
    iDestruct (IHΓ with "[HΓ]") as "[_ $]"; eauto.
  Qed.

  Lemma interp_env_length Γ Θ ρ vs :
    ⟦ Γ ⟧* Θ ρ vs -∗ ⌜length Γ = length vs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Fixpoint bi_subsume_un t Θ ρ vv {struct t} :
    envs_Persistent Θ →
    env_coherent Θ ∗
    ⟦ t ⟧ Θ ρ vv ⊢ ⌊ t ₗ⌋ (projl Θ) ρ vv.1 ∧ ⌊ t ᵣ⌋ (projr Θ) ρ vv.2
  with secbin_subsumes_secun τ Θ ρ vv {struct τ} :
    envs_Persistent Θ →
    env_coherent Θ ∗
    ⟦ τ ⟧ₛ Θ ρ vv ⊢ ⌊ τ ₗ⌋ₛ (projl Θ) ρ vv.1 ∧ ⌊ τ ᵣ⌋ₛ (projr Θ) ρ vv.2.
  Proof.
    - iIntros (Hpers) "[#Hcoh #H]". destruct t.
      + rewrite !interp_un_unit_def /=.
        by iDestruct "H" as "[-> ->]".
      + rewrite !interp_un_bool_def /=.
        iDestruct "H" as (b1 b2) "[-> [-> ->]]". by iSplit; iExists _.
      + rewrite !interp_un_nat_def /=.
        iDestruct "H" as (n1 n2) "[-> [-> ->]]". by iSplit; iExists _.
      + rewrite /= !interp_un_tvar_def !list_lookup_fmap.
        destruct vv, (Θ !! x) eqn:Heq; rewrite Heq /=; [|done].
        iDestruct (big_sepL_lookup with "Hcoh") as "#Hlookup"; [done|].
        iApply ("Hlookup" $! (_,_) with "H").
      + rewrite interp_ref_def !interp_un_ref_def. destruct τ.
        iDestruct "H" as ([l1 l2]) "[-> #Hinv]". iSplit.
        * iModIntro. iExists (nroot.@(l1, l2)), _.
          iSplit; [done|]. case_bool_decide.
          { iIntros (??).
            iInv (nroot .@ (l1, l2)) as "Hl" "Hclose". do 2 iModIntro.
            iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & #Hτ)".
            rewrite !interp_sec_def bool_decide_eq_true_2 //.
            iDestruct (bi_subsume_un with "[$Hcoh $Hτ]") as "[#? #?]".
            iExists _. rewrite interp_un_sec_def.
            iFrame; iFrame "#". iDestruct 1 as "[Hl1 _]".
            iMod ("Hclose" with "[-]") as "_"; [|done]. iNext.
            iExists _, _. iFrame.
            rewrite interp_sec_def bool_decide_eq_true_2 //. }
          { iIntros (??).
            iInv (nroot .@ (l1, l2)) as "Hl" "Hclose". do 2 iModIntro.
            iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & #Hτ)".
            rewrite !interp_sec_def bool_decide_eq_false_2 //.
            iDestruct "Hτ" as "[#? #?]".
            iSplitL "Hl1"; [auto|].
            iDestruct 1 as (w) "[Hl1 #?]".
            iMod ("Hclose" with "[-]"); [|done].
            iNext; iExists _,_; iFrame.
            rewrite !interp_sec_def bool_decide_eq_false_2 //. iFrame "#". }
        * (* symmetric to the case above *)
          iModIntro; iExists (nroot.@(l1, l2)), _.
          iSplit; [done|]. case_bool_decide.
         { iIntros (??).
           iInv (nroot .@ (l1, l2)) as "Hl" "Hclose". do 2 iModIntro.
           iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & #Hτ)".
           rewrite !interp_sec_def bool_decide_eq_true_2 //.
           iDestruct (bi_subsume_un with "[$Hcoh $Hτ]") as "[#? #?]".
           iExists _. rewrite interp_un_sec_def.
           iFrame; iFrame "#". iDestruct 1 as "[Hl2 _]".
           iMod ("Hclose" with "[-]") as "_"; [|done]. iNext.
           iExists _, _. iFrame.
           rewrite interp_sec_def bool_decide_eq_true_2 //. }
         { iIntros (??).
           iInv (nroot .@ (l1, l2)) as "Hl" "Hclose". do 2 iModIntro.
           iDestruct "Hl" as (w1 w2) "(Hl1 & Hl2 & #Hτ)".
           rewrite !interp_sec_def bool_decide_eq_false_2 //.
           iDestruct "Hτ" as "[#? #?]".
           iSplitL "Hl2"; [auto|].
           iDestruct 1 as (w) "[Hl2 #?]".
           iMod ("Hclose" with "[-]"); [|done].
           iNext; iExists _,_; iFrame.
           rewrite !interp_sec_def bool_decide_eq_false_2 //. iFrame "#". }
      + cbn. iDestruct "H" as "#(?&Hτ1&Hτ2)". iFrame "#".
      + cbn. iDestruct "H" as (????) "[-> [-> #[Hτ1 Hτ2]]]".
        iDestruct (secbin_subsumes_secun with "[$Hτ1 $Hcoh]") as "[#? #?]".
        iDestruct (secbin_subsumes_secun with "[$Hτ2 $Hcoh]") as "[#? #?]".
        rewrite !interp_un_prod_def. iSplit; iExists _, _; eauto.
      + cbn. rewrite !interp_un_sum_def.
        iDestruct "H" as (??) "#[ [-> #Hτ1] | [-> #Hτ2] ]".
        * iDestruct (secbin_subsumes_secun with "[$Hτ1 $Hcoh]") as "[? ?]"; auto.
        * iDestruct (secbin_subsumes_secun with "[$Hτ2 $Hcoh]") as "[? ?]"; auto.
      + cbn. iDestruct "H" as "#[_ [? ?]]". auto.
      + cbn. iDestruct "H" as "#[_ [? ?]]". auto.
      + cbn. iDestruct "H" as (τR τi1 τi2) "(% & % & % & [#Hsubsum #H])".
        iDestruct "H" as ([w1 w2]) "(-> & -> & Hτ)".
        iDestruct (secbin_subsumes_secun with "[$]") as "[#? #?] /=".
        rewrite !interp_un_exist_def.
        iSplit; iModIntro; [iExists τi1| iExists τi2]; eauto.
      + change (fixpoint _) with (⟦ TRec τ ⟧ Θ ρ).
        iLöb as "IH" forall (vv) "H".
        rewrite {2}interp_rec_def fixpoint_interp_rec1_eq.
        iDestruct "H" as (ww) "[-> #Hτ]".
        change (fixpoint _) with (⟦ TRec τ ⟧ Θ ρ).
        iEval (rewrite !interp_un_rec_def).
        rewrite !fixpoint_interp_un_rec1_eq /=. iSplit.
        * iModIntro. iExists _. iSplit; [done|]. iModIntro.
          iDestruct ((secbin_subsumes_secun τ
            ((⟦ TRec τ ⟧ Θ ρ, (⌊ TRec τ ₗ⌋ Θ.*2.*1 ρ, ⌊ TRec τ ᵣ⌋ Θ.*2.*2 ρ)) :: Θ))
                       with "[$Hcoh]") as "[? ?]"; [|done].
          cbn. iSplit; [|done]. iModIntro.
          iIntros (?) "#?". by iApply "IH".
        * iModIntro. iExists _. iSplit; [done|]. iModIntro.
          iDestruct ((secbin_subsumes_secun τ
            ((⟦ TRec τ ⟧ Θ ρ, (⌊ TRec τ ₗ⌋ Θ.*2.*1 ρ, ⌊ TRec τ ᵣ⌋ Θ.*2.*2 ρ)) :: Θ))
                       with "[$Hcoh]") as "[? ?]"; [|done].
          cbn. iSplit; [|done]. iModIntro.
          iIntros (?) "#?". by iApply "IH".
    - iIntros (?) "[#Hcoh #H]".
      destruct τ. rewrite !interp_un_sec_def /=. case_bool_decide.
      + iApply (bi_subsume_un with "[$H $Hcoh]").
      + rewrite !interp_un_sec_def //.
  Qed.

  Lemma interp_env_bi_un  Γ Θ ρ (vvs : list (val * val)) :
    envs_Persistent Θ →
    env_coherent Θ ∗
    ⟦ Γ ⟧* Θ ρ vvs ⊢ ⌊ Γ ₗ⌋* (projl Θ) ρ vvs.*1 ∧ ⌊ Γ ᵣ⌋* (projr Θ) ρ vvs.*2.
  Proof.
    revert vvs. induction Γ.
    - iIntros (vvs ?) "[#Hcoh [%Hl _]] /=".
      symmetry in Hl. apply nil_length_inv in Hl. subst.
      iSplit; iApply interp_un_env_nil.
    - iIntros ([] ?) "[#Hcoh #HaΓ] /=".
      { by iDestruct "HaΓ" as "[% _]". }
      iDestruct (interp_env_cons with "HaΓ") as "[#Ha #HΓ]".
      iDestruct (secbin_subsumes_secun with "[$Ha $Hcoh]") as "[#Ha1 #Ha2]".
      iDestruct (IHΓ with "[$HΓ $Hcoh]") as "[#HΓ1 #HΓ2]".
      iSplitL; iApply interp_un_env_cons; iFrame "#".
  Qed.

  Lemma interp_bi_label_weaken t ρ1 ξ ρ2 Θ :
    ⟦ t.|[upn (length ρ1) (ren (+ length ξ))] ⟧ Θ (ρ1 ++ ξ ++ ρ2 : listO labelO)
    ≡ ⟦ t ⟧ Θ (ρ1 ++ ρ2)
  with interp_sec_bi_label_weaken τ ρ1 ξ ρ2 Θ :
    ⟦ hsubst (inner := label_term)
      (upn (length ρ1) (ren (+ length ξ))) τ ⟧ₛ Θ (ρ1 ++ ξ ++ ρ2 : listO labelO)
    ≡ ⟦ τ ⟧ₛ Θ (ρ1 ++ ρ2).
  Proof.
    - destruct t; [done|done|done|done|..]; cbn.
      + move=>?. properness; auto. rewrite /interp_ref_inv.
        properness; auto; [|apply: interp_un_sec_label_weaken..].
        apply: interp_sec_bi_label_weaken.
      + move=>?. properness; auto.
        * apply: interp_sec_bi_label_weaken.
        * rewrite /interp_expr. do 4 f_equiv. apply interp_sec_bi_label_weaken.
        * apply: (interp_un_label_weaken (TArrow _ _ _)).
        * apply: (interp_un_label_weaken (TArrow _ _ _)).
     + move=>?. properness; auto; apply interp_sec_bi_label_weaken.
     + move=>?. properness; auto; apply interp_sec_bi_label_weaken.
     + move=>?. properness; auto.
       * rewrite /interp_expr. do 4 f_equiv. apply interp_sec_bi_label_weaken.
       * apply: (interp_un_label_weaken (TForall _ _)).
       * apply: (interp_un_label_weaken (TForall _ _)).
     + move=>?. properness; auto.
       * asimpl. rewrite /interp_expr. do 4 f_equiv. cbn.
         apply (interp_sec_bi_label_weaken _ (_ :: _)).
       * apply: (interp_un_label_weaken (TLForall _ _)).
       * apply: (interp_un_label_weaken (TLForall _ _)).
     + move=>?. properness; auto. apply interp_sec_bi_label_weaken.
     + properness; auto.
       rewrite !(interp_un_label_weaken (TRec τ)).
       apply interp_sec_bi_label_weaken.
   - destruct τ=>? /=. rewrite interp_label_weaken //. f_equiv.
     + apply interp_bi_label_weaken.
     + f_equiv; apply: interp_un_label_weaken.
  Qed.

  Lemma interp_bi_label_ren t Θ ρ ℓ :
    ⟦ t.|[ren (+1)] ⟧ Θ (ℓ :: ρ) ≡ ⟦ t ⟧ Θ ρ.
  Proof. move=>?. apply (interp_bi_label_weaken _ [] [_]). Qed.

  Lemma interp_bi_label_subst_up t Θ ℓ ρ1 ρ2 :
    ⟦ t.|[upn (length ρ1) (ℓ .: ids)] ⟧ Θ (ρ1 ++ ρ2)
    ≡  ⟦ t ⟧ Θ (ρ1 ++ ⌊ ℓ ⌋ₗ ρ2 :: ρ2)
  with interp_sec_bi_label_subst_up τ Θ ℓ ρ1 ρ2 :
    ⟦ hsubst (inner := label_term)
      (upn (length ρ1) (ℓ .: ids)) τ ⟧ₛ Θ (ρ1 ++ ρ2)
    ≡ ⟦ τ ⟧ₛ Θ (ρ1 ++ ⌊ ℓ ⌋ₗ ρ2 :: ρ2).
  Proof.
    - destruct t; [done|done|done|done|..]; cbn.
      + move=>?. rewrite /interp_ref_inv.
        properness; auto; [|apply: interp_un_sec_label_subst_up..].
        apply interp_sec_bi_label_subst_up.
      + move=>?. properness; auto.
        * apply: interp_sec_bi_label_subst_up.
        * rewrite /interp_expr. do 4 f_equiv. apply interp_sec_bi_label_subst_up.
        * apply: (interp_un_label_subst_up (TArrow _ _ _)).
        * apply: (interp_un_label_subst_up (TArrow _ _ _)).
      + move=>?. properness; auto; apply interp_sec_bi_label_subst_up.
      + move=>?. properness; auto; apply interp_sec_bi_label_subst_up.
      + move=>?. properness; auto.
        * rewrite /interp_expr. do 4 f_equiv. apply interp_sec_bi_label_subst_up.
        * apply: (interp_un_label_subst_up (TForall _ _)).
        * apply: (interp_un_label_subst_up (TForall _ _)).
     + move=>?. properness; auto.
       * asimpl. rewrite /interp_expr. do 4 f_equiv. cbn.
         apply (interp_sec_bi_label_subst_up _ _ _ (_ :: _)).
        * apply: (interp_un_label_subst_up (TLForall _ _)).
        * apply: (interp_un_label_subst_up (TLForall _ _)).
     + move=>?. properness; auto. apply interp_sec_bi_label_subst_up.
     + properness; auto. rewrite 2!(interp_un_label_subst_up (TRec τ)).
       apply interp_sec_bi_label_subst_up.
   - destruct τ=>? /=. rewrite interp_label_subst_up. f_equiv.
     + apply interp_bi_label_subst_up.
     + f_equiv; apply: interp_un_label_subst_up.
  Qed.

  Fixpoint interp_type_weaken t Θ1 Π Θ2 n m ρ {struct t} :
    n = length Θ1 →
    m = length Π →
    ⟦ t.[upn n (ren (+m))] ⟧ (Θ1 ++ Π ++ Θ2) ρ ≡ ⟦ t ⟧ (Θ1 ++ Θ2) ρ
  with interp_sec_type_weaken τ Θ1 Π Θ2 n m ρ {struct τ} :
    n = length Θ1 →
    m = length Π →
    ⟦ τ.|[upn n (ren (+ m))] ⟧ₛ (Θ1 ++ Π ++ Θ2) ρ ≡ ⟦ τ ⟧ₛ (Θ1 ++ Θ2) ρ.
  Proof.
    - intros -> ->. destruct t; [done|done|done|..]; cbn.
      + rewrite iter_up; destruct lt_dec as [Hl | Hl].
        { rewrite !interp_tvar_def !list_lookup_fmap !lookup_app_l //. }
        rewrite !interp_tvar_def /=.
        rewrite !list_lookup_fmap !(lookup_app_r (A := T)); [|lia ..].
        do 3 f_equiv. lia.
      + destruct τ=>?. rewrite /interp_ref_inv. properness; auto.
        cbn. f_equiv; [by apply: interp_type_weaken|].
        rewrite !fmap_app. f_equiv; apply: interp_un_type_weaken; rewrite !fmap_length //.
      + move=>?. rewrite !fmap_app. properness; auto.
        * apply interp_sec_type_weaken => //.
        * rewrite /interp_expr. do 4 f_equiv; cbn. apply interp_sec_type_weaken => //.
        * apply (interp_un_type_weaken (TArrow _ _ _)); rewrite !fmap_length //.
        * apply (interp_un_type_weaken (TArrow _ _ _)); rewrite !fmap_length //.
     + move=>?. properness; auto; apply interp_sec_type_weaken=>//.
     + move=>?. properness; auto; apply interp_sec_type_weaken=>//.
     + move=>?. rewrite !fmap_app. properness; auto.
       * asimpl. rewrite /interp_expr. do 4 f_equiv. cbn.
         apply (interp_sec_type_weaken _ (_ :: _)) =>//.
       * apply (interp_un_type_weaken (TForall _ _)); rewrite !fmap_length //.
       * apply (interp_un_type_weaken (TForall _ _)); rewrite !fmap_length //.
     + move=>?. rewrite !fmap_app. properness; auto.
       * rewrite /interp_expr. do 4 f_equiv; cbn.
         rewrite -!up_hcomp_n_internal; [|apply up_hcomp_dist].
         asimpl. apply interp_sec_type_weaken => //.
       * apply: (interp_un_type_weaken (TLForall _ _)); rewrite !fmap_length //.
       * apply: (interp_un_type_weaken (TLForall _ _)); rewrite !fmap_length //.
     + move=>?. properness; auto. asimpl.
       apply (interp_sec_type_weaken _ (_ :: _)) =>//.
     + properness; auto. rewrite !fmap_app.
       rewrite !(interp_un_type_weaken (TRec τ)) ?fmap_length //.
       asimpl. apply (interp_sec_type_weaken _ (_ :: _)) => //.
    - intros -> -> ?. destruct τ => /=. f_equiv.
       + apply interp_type_weaken=>//.
       + rewrite !fmap_app.
         f_equiv; apply: interp_un_type_weaken; rewrite !fmap_length //.
  Qed.

  Fixpoint interp_type_subst_up t (Θ1 Θ2 : listO T) ρ t' {struct t} :
    ⟦ t ⟧ (Θ1 ++ (⟦ t' ⟧ Θ2 ρ, (⌊ t' ₗ⌋ (projl Θ2) ρ, ⌊ t' ᵣ⌋ (projr Θ2) ρ)) :: Θ2) ρ
    ≡ ⟦ t.[upn (length Θ1) (t' .: ids)] ⟧ (Θ1 ++ Θ2) ρ
  with interp_sec_type_subst_up τ (Θ1 Θ2 : listO T) ρ t' {struct τ} :
    ⟦ τ ⟧ₛ (Θ1 ++ (⟦ t' ⟧ Θ2 ρ, (⌊ t' ₗ⌋ (projl Θ2) ρ, ⌊ t' ᵣ⌋ (projr Θ2) ρ)) :: Θ2) ρ
    ≡ ⟦ τ.|[upn (length Θ1) (t' .: ids)] ⟧ₛ (Θ1 ++ Θ2) ρ.
  Proof.
    - destruct t; [done|done|done|..]; cbn.
      + rewrite iter_up; destruct lt_dec as [Hl | Hl]=> /=.
        { rewrite !list_lookup_fmap !lookup_app_l //. }
        asimpl.
        rewrite !list_lookup_fmap !(lookup_app_r (A := T)); [|lia ..].
        case EQ: (x - length Θ1) => [|m]; simpl.
        { symmetry. apply (interp_type_weaken _ [] _ _ 0) => //. }
        rewrite !list_lookup_fmap !(lookup_app_r (A := T)); [| lia..].
        assert (strings.length Θ1 + m - strings.length Θ1 = m) as Heq by lia.
        by rewrite Heq.
      + move=>?. rewrite /interp_ref_inv. cbn.
        properness; auto. apply interp_sec_type_subst_up.
      + move=>?. rewrite /interp_expr !fmap_app. cbn. properness; auto.
        * apply interp_sec_type_subst_up.
        * do 4 f_equiv. apply interp_sec_type_subst_up.
        * apply: interp_un_type_subst_up; rewrite !fmap_length //.
        * apply: interp_un_type_subst_up; rewrite !fmap_length //.
      + move=>?. properness; auto; apply interp_sec_type_subst_up.
      + move=>?. properness; auto; apply interp_sec_type_subst_up.
      + move=>?. rewrite /interp_expr !fmap_app. cbn. properness; auto.
        * do 4 f_equiv. apply (interp_sec_type_subst_up _ (_ :: _)).
        * apply: interp_un_type_subst_up; rewrite !fmap_length //.
        * apply: interp_un_type_subst_up; rewrite !fmap_length //.
      + move=>?. rewrite /interp_expr !fmap_app. properness; auto.
        * do 4 f_equiv.
          rewrite -!up_hcomp_n_internal; [|apply up_hcomp_dist]. asimpl.
          rewrite -!(interp_un_label_ren t' ) -interp_bi_label_ren.
          apply interp_sec_type_subst_up.
       * apply: interp_un_type_subst_up; rewrite !fmap_length //.
       * apply: interp_un_type_subst_up; rewrite !fmap_length //.
      + move=>?. properness; auto. apply (interp_sec_type_subst_up _ (_ :: _)).
     + properness; auto. rewrite !fmap_app.
       rewrite !(interp_un_type_subst_up) ?fmap_length //.
       asimpl. apply (interp_sec_type_subst_up _ (_ :: _)).
   - destruct τ=>? => /=. f_equiv.
    + apply interp_type_subst_up.
    + rewrite !fmap_app.
      f_equiv; apply: interp_un_type_subst_up; rewrite ?fmap_length //.
  Qed.

  Lemma interp_bi_env_ren Θ ρ Γ vvs τR :
    ⟦ hsubst_sectype (ren (+1)) <$> Γ ⟧* (τR :: Θ) ρ vvs ⊣⊢ ⟦ Γ ⟧* Θ ρ vvs.
  Proof.
    apply bi.sep_proper; [apply bi.pure_proper; by rewrite fmap_length|].
    revert vvs τR; induction Γ; intros [|v vs] τR; csimpl; auto.
    apply bi.sep_proper; auto. apply (interp_sec_type_weaken _ [] [_] _ 0) => //.
  Qed.

  Lemma interp_bi_env_label_ren Θ ρ Γ vs ℓ :
    ⟦ hsubst_label_sectype (ren (+1)) <$> Γ ⟧* Θ (ℓ :: ρ) vs ⊣⊢ ⟦ Γ ⟧* Θ ρ vs.
  Proof.
    apply bi.sep_proper; [apply bi.pure_proper; by rewrite fmap_length|].
    revert ρ vs ℓ; induction Γ=> ρ [|v vs] ℓ; csimpl; auto.
    apply bi.sep_proper; auto. by apply (interp_sec_bi_label_weaken _ [] [ℓ] _).
  Qed.

End logrel.

Notation "⟦ t ⟧" := (interp t).
Notation "⟦ τ ⟧ₛ" := (interp_sec τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr ⟦ τ ⟧ₛ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

Typeclasses Opaque interp.
Typeclasses Opaque interp_sec.
Typeclasses Opaque interp_env.
Global Opaque interp_env.
Global Opaque interp_sec.
Global Opaque interp.

Tactic Notation "uunits" :=
  rewrite ?interp_sec_def ?interp_unit_def
          ?interp_un_sec_def ?interp_un_unit_def.
Tactic Notation "unats" :=
  rewrite ?interp_sec_def ?interp_nat_def
          ?interp_un_sec_def ?interp_un_nat_def.
Tactic Notation "ubools" :=
  rewrite ?interp_sec_def ?interp_bool_def
          ?interp_un_sec_def ?interp_un_bool_def.
Tactic Notation "uarrows" :=
  rewrite ?interp_sec_def ?interp_arrow_def
          ?interp_un_sec_def ?interp_un_arrow_def.
Tactic Notation "utforalls" :=
  rewrite ?interp_sec_def ?interp_tforall_def
          ?interp_un_sec_def ?interp_un_tforall_def.
Tactic Notation "utvars" :=
  rewrite ?interp_sec_def ?interp_tvar_def
          ?interp_un_sec_def ?interp_un_tvar_def.
