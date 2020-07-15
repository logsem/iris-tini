From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From IC Require Export reduction base.
Import uPred.

Inductive Prod :=
| PrNil : Prod
| PrCons : Type → Prod → Prod.

Notation "'[Prod' ]" := PrNil (format "[Prod ]") : type_scope.
Notation "'[Prod' x ]" := (PrCons x PrNil) (format "[Prod  x ]") : type_scope.
Notation "'[Prod' x ; y ; .. ; z ]" :=
  (PrCons x (PrCons y .. (PrCons z PrNil) ..))
    (format "[Prod  x ;  y ;  .. ;  z ]") : type_scope.

Fixpoint TypeOfProd (a : Prod) : Type :=
match a with
| PrNil => unit
| PrCons A b =>
  match b with
  | PrNil => A
  | _ => A * TypeOfProd b
  end
end.

Global Coercion TypeOfProd : Prod >-> Sortclass.

Fixpoint Prod_fun (a : Prod) (B : Type) : Type :=
match a with
| PrNil => B
| PrCons A b =>
  match b with
  | PrNil => A → B
  | _ => A → (Prod_fun b B)
  end
end.

Fixpoint to_Prod_fun {a : Prod} {B : Type} (f : a → B) {struct a} :
  Prod_fun a B :=
match a as u return (u → B) → Prod_fun u B with
| PrNil => λ g, g tt
| PrCons A b =>
  match b as v return
        ((v → B) → Prod_fun v B) →
        (PrCons A v → B) → Prod_fun (PrCons A v) B with
  | PrNil => λ F g x, g x
  | PrCons C p => λ F g x, F (λ y, g (x, y))
  end (@to_Prod_fun b B)
end f.

Fixpoint from_Prod_fun {a : Prod} {B : Type} (f : Prod_fun a B) : a → B :=
match a as u return Prod_fun u B → u → B with
| PrNil => λ y _, y
| PrCons A b =>
  match b as v return
        (Prod_fun v B → v → B) →
        (Prod_fun (PrCons A v) B) → (PrCons A v) → B with
  | PrNil => λ F g x, g x
  | PrCons C p => λ F g x, F (g (fst x)) (snd x)
  end (@from_Prod_fun b B)
end f.

Record ICData (Λ : language) (Σ : gFunctors) := Build_ICData {
  ICD_Extra : Prod;
  ICD_state_interp : state Λ → iProp Σ;
  ICD_modality_index : Prod;
  ICD_modality_bind_condition :
    ICD_modality_index →
    ICD_modality_index →
    (ICD_Extra → ICD_modality_index) →
    (ICD_Extra → ICD_Extra → ICD_Extra) → Prop;
  ICD_modality :
    ICD_modality_index → coPset → nat → (ICD_Extra → iProp Σ) → iProp Σ;
}.

Class ICC {Λ Σ} (ICD : ICData Λ Σ) := Build_IRG {
  ICC_Extra : Prod := ICD_Extra _ _ ICD;
  ICC_state_interp : state Λ → iProp Σ := ICD_state_interp _ _ ICD;
  ICC_modality_index : Prod := ICD_modality_index _ _ ICD;
  ICC_modality :
    ICC_modality_index → coPset → nat → (ICC_Extra → iProp Σ) → iProp Σ :=
    ICD_modality _ _ ICD;
  ICC_modality_ne :>
    ∀ idx E m n, Proper (pointwise_relation _ (dist m) ==> (dist m))
                      (λ f, ICC_modality idx E n f);
  ICC_modality_mono :
    ∀ idx E1 E2 n Φ Ψ,
      E1 ⊆ E2 → (∀ x, Φ x -∗ Ψ x)
        ⊢ ICC_modality idx E1 n Φ -∗ ICC_modality idx E2 n Ψ;
  (* The modality must be a monad *)
  ICC_modality_intro :
    ∀ idx E n Φ, ICC_modality idx E 0 Φ ⊢ ICC_modality idx E n Φ;
  ICC_modality_bind_condition :
    ICC_modality_index →
    ICC_modality_index →
    (ICC_Extra → ICC_modality_index) →
    (ICC_Extra → ICC_Extra → ICC_Extra) → Prop :=
    ICD_modality_bind_condition _ _ ICD;
  ICC_modality_bind : ∀ idx idx' f g E n m Φ,
      ICC_modality_bind_condition idx idx' f g →
      ICC_modality idx' E n (λ x, ICC_modality (f x) E m (λ z, Φ (g x z)))
      ⊢ ICC_modality idx E (n + m) Φ;
}.

Global Arguments ICC_state_interp {_ _} _ {_} _ : simpl never.
Global Arguments ICC_modality {_ _} _ {_} _ _ _ : simpl never.
Global Arguments ICC_modality_bind_condition {_ _} _ {_} : simpl never.

Class ICMIsOuterModal {Λ Σ} (icd : ICData Λ Σ) `{!ICC icd} idx
      (M : coPset → nat → iProp Σ → iProp Σ) :=
  IC_modality_is_outer_modal :
    ∀ E n P, M E n (ICC_modality icd idx E n P) ⊢ (ICC_modality icd idx E n P).

Class ICMIsInnerModal {Λ Σ} (icd : ICData Λ Σ) `{!ICC icd} idx
      (M : coPset → nat → iProp Σ → iProp Σ) :=
  IC_modality_is_inner_modal :
    ∀ E n P, (ICC_modality icd idx E n (λ x, M E n (P x)))
               ⊢ (ICC_modality icd idx E n P).

Class ICMAlwaysSupportsShift
      {Λ Σ} `{!invG Σ} (icd : ICData Λ Σ) `{!ICC icd} idx :=
  IC_always_supports_shift : ∀ n E1 E2 P,
    (|={E1, E2}=> ICC_modality icd idx E2 n (λ x, |={E2, E1}=> P x))
      ⊢ (ICC_modality icd idx E1 n P).

Class ICMSupportsAtomicShift
      {Λ Σ} `{!invG Σ} (icd : ICData Λ Σ) `{!ICC icd} idx :=
  IC_supports_atomic_shift : ∀ n E1 E2 P, n ≤ 1 →
    (|={E1, E2}=> ICC_modality icd idx E2 n (λ x, |={E2, E1}=> P x))
      ⊢ (ICC_modality icd idx E1 n P).

Global Instance ICMAlwaysSupportsAtomicShift
       {Λ Σ} `{!invG Σ} (icd : ICData Λ Σ) `{!ICC icd} idx :
  ICMAlwaysSupportsShift icd idx → ICMSupportsAtomicShift icd idx.
Proof. rewrite /ICMAlwaysSupportsShift /ICMSupportsAtomicShift; auto. Qed.

Class ICMSplitForStep {Λ Σ} (icd : ICData Λ Σ) `{!ICC icd} idx :=
{
  ICM_split_for_step_M1 : coPset → iProp Σ → iProp Σ;
  ICM_split_for_step_M2 : coPset → iProp Σ → iProp Σ;
  ICM_split_for_step_split n E P :
    ICM_split_for_step_M1 E
     (ICM_split_for_step_M2 E
      (ICC_modality icd idx E n P))  ⊢ ICC_modality icd idx E (S n) P;
  ICM_split_for_step_M1_mono E P Q :
    (P -∗ Q) ⊢ ICM_split_for_step_M1 E P -∗ ICM_split_for_step_M1 E Q;
  ICM_split_for_step_M2_mono E P Q :
    (P -∗ Q) ⊢ ICM_split_for_step_M2 E P -∗ ICM_split_for_step_M2 E Q;
}.

Class ICCMElimCond n m := ICC_modality_elim_cond : n ≤ m.

Global Hint Extern 10 (ICCMElimCond _ _) =>
  unfold ICCMElimCond; (lia || eassumption): typeclass_instances.

Typeclasses Opaque ICC_state_interp ICC_modality.

Global Instance ICC_modality_from_modal {Λ Σ} (icd : ICData Λ Σ)
       `{!ICC icd} idx (Φ : ICC_Extra → iProp Σ) E n :
  FromModal modality_id (True : Prop) (ICC_modality icd idx E n Φ)
            (ICC_modality icd idx E 0 Φ).
Proof.
  rewrite /FromModal. iIntros "HP"; simpl.
  by iApply ICC_modality_intro.
Qed.

Global Instance ICC_modality_mono'  {Λ Σ} (icd : ICData Λ Σ)
       `{!ICC icd} idx E n :
  Proper (pointwise_relation _ bi_entails ==> bi_entails) (λ f, ICC_modality icd idx E n f).
Proof.
  iIntros (P Q HPQ). iApply ICC_modality_mono; first done.
  iIntros (x); iApply HPQ.
Qed.

Global Instance ICC_modality_elim_fupd {Λ Σ} (icd : ICData Λ Σ)
       `{!ICC icd} idx `{!invG Σ} `{!ICMIsOuterModal icd idx (λ E n P, |={E}=> P)%I}
       (P : iProp Σ) (Φ : ICC_Extra → iProp Σ) p E E' n :
  ElimModal True p false (|={E, E'}=> P) P
            (ICC_modality icd idx E n Φ) (|={E', E}=> ICC_modality icd idx E n Φ).
Proof.
  rewrite /ElimModal /=.
  iIntros (?) "[HP HPQ]"; rewrite intuitionistically_if_elim.
  iApply IC_modality_is_outer_modal. iMod "HP".
  by iMod ("HPQ" with "HP").
Qed.

Global Instance ICC_modality_elim_is_bupd {Λ Σ} (icd : ICData Λ Σ)
       `{!ICC icd} idx `{!ICMIsOuterModal icd idx (λ E n P, |==> P)%I}
       (P : iProp Σ) (Φ : ICC_Extra → iProp Σ) p E n :
  ElimModal True p false (|==> P) P
            (ICC_modality icd idx E n Φ) (|==> ICC_modality icd idx E n Φ).
Proof.
  rewrite /ElimModal /=.
  iIntros (?) "[HP HPQ]"; rewrite intuitionistically_if_elim.
  iApply IC_modality_is_outer_modal. iMod "HP".
  by iMod ("HPQ" with "HP").
Qed.

Class ExecutesPurely {Λ} (e : expr Λ) := executes_purely :
    ∀ σ1 σ2 v n, relations.nsteps pstep n (e, σ1) (of_val v, σ2) → σ1 = σ2.

Class PureLang Λ := pure_language :
    ∀ (e1 : expr Λ) σ1 σ2 e2, pstep (e1, σ1) (e2, σ2) → σ1 = σ2.

Global Instance PureLang_ExecutesPurely `{! PureLang Λ} (e : expr Λ) :
  ExecutesPurely e.
Proof.
  intros σ1 σ2 v n; revert e σ1 σ2 v.
  induction n; intros e σ1 σ2 v Hr.
  { by inversion Hr; simplify_eq. }
  inversion Hr as [|? ? [e' σ'] ? Hps]; simpl in *; simplify_eq.
  apply pure_language in Hps; subst.
  eauto.
Qed.

Definition ic_def {Λ Σ} (icd: ICData Λ Σ) `{!ICC icd}
           idx E e (Φ : val Λ → nat → ICC_Extra → iProp Σ) : iProp Σ :=
  (∀ σ1 σ2 v n,
      ⌜relations.nsteps pstep n (e, σ1) (of_val v, σ2)⌝ -∗
       ICC_state_interp icd σ1 -∗
       ICC_modality icd idx E n (λ x, Φ v n x ∗ ICC_state_interp icd σ2))%I.
Definition ic_aux : seal (@ic_def). Proof. by eexists. Qed.
Definition ic {Λ Σ} RM idx {H} E e Φ := ic_aux.(unseal) Λ Σ RM idx H E e Φ.
Definition ic_eq : @ic = @ic_def := ic_aux.(seal_eq).

Arguments ic {_ _} _ {_} _ _ _%E _.
Instance: Params (@ic) 8 := {}.

Notation "'IC@{' R , idx } e @ E {{ Φ } }" := (ic R idx E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v ; n , Q } }" :=
  (ic R idx E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v , Φ } }" :=
  (ic R idx E e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v ; n | [ x ] , Q } }" :=
  (ic R idx E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v ; n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R idx E e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x, .. (λ y, Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v | [ x ] , Q } }" :=
  (ic R idx E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (ic R idx E e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'IC@{' R , idx } e {{ Φ } }" := (ic R idx ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v ; n , Q } }" :=
  (ic R idx ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v , Φ } }" :=
  (ic R idx ⊤ e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v ; n | [ x ] , Q } }" :=
  (ic R idx ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R idx ⊤ e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v | [ x ] , Q } }" :=
  (ic R idx ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  idx }  e  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R , idx } e {{ v | x ; .. ; y , Φ } }" :=
  (ic R idx ⊤ e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  idx }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'IC@{' R } e @ E {{ Φ } }" :=
  (ic R tt E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ Φ } }" := (ic R tt E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v ; n , Q } }" :=
  (ic R tt E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v , Φ } }" :=
  (ic R tt E e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v ; n | [ x ] , Q } }" :=
  (ic R tt E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  @  E  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R tt E e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v | [ x ] , Q } }" :=
  (ic R tt E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  @  E  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (ic R tt E e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'IC@{' R } e {{ Φ } }" :=
  (ic R tt ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R }  e  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R } e {{ v ; n , Q } }" :=
  (ic R tt ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e {{ v , Φ } }" :=
  (ic R tt ⊤ e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R } e {{ v ; n | [ x ] , Q } }" :=
  (ic R tt ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R tt ⊤ e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'IC@{' R } e {{ v | [ x ] , Q } }" :=
  (ic R tt ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R }  e  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'IC@{' R } e {{ v | x ; .. ; y , Φ } }" :=
  (ic R tt ⊤ e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R , [ idx .. idy idz ] }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v ; n , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) E e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v ; n | [ x ] , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. )
      E e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v | [ x ] , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. )
      E e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.


Notation "'IC@{' R , [ idx .. idy idz ] } e {{ Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'IC@{' R , [ idx .. idy idz ] }  e  {{  Φ  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v ; n , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v ; n | [ x ] , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. )
      ⊤ e%E (λ v n r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v | [ x ] , Q } }" :=
  (ic R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'IC@{' R , [ idx .. idy idz ] } e {{ v | x ; .. ; y , Φ } }" :=
  (ic R (pair idx .. (pair idy idz) .. )
      ⊤ e%E (λ v _ r, @from_Prod_fun (@ICC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'IC@{' R ,  [ idx .. idy idz ] }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.


(* Texan IC triples *)
Notation "'{{{|' P '|}}}@{' R , idx } e @ E {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ IC@{R, idx} e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R ,  idx }  e  @  E  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R } e @ E {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ IC@{R} e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R }  e  @  E  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R , idx } e {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ IC@{R, idx} e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R ,  idx }  e  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R } e {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ IC@{R} e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R }  e  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Section ic.
Context `(icd : ICData Λ Σ) `{!ICC icd}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → nat → ICC_Extra → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Global Instance ic_ne idx E e n :
  Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n))) ==> dist n)
         (@ic Λ Σ icd _ idx E e).
Proof.
  intros Φ1 Φ2 R; rewrite ic_eq /ic_def.
  do 10 f_equiv.
  apply ICC_modality_ne; f_equiv.
  repeat f_equiv; apply R.
Qed.

Global Instance ic_proper idx E e :
  Proper (pointwise_relation
            _ (pointwise_relation _ (pointwise_relation _ (≡))) ==> (≡))
         (@ic Λ Σ icd _ idx E e).
Proof.
  intros Φ Φ' R.
  apply equiv_dist=>m; apply ic_ne =>v k x. by rewrite R.
Qed.

Lemma ic_intro idx E e `{!ExecutesPurely e} Φ :
  (∀ v n, ICC_modality icd idx E n (Φ v n)) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  rewrite ic_eq /ic_def.
  iIntros "HΦ".
  iIntros (σ1 σ2 v n Hr) "Hsi".
  iSpecialize ("HΦ" $! v n).
  iApply (ICC_modality_mono with "[Hsi]"); try done.
  iIntros (x) "?".
  rewrite (executes_purely _ _ _ _ Hr); iFrame.
Qed.

Lemma ic_value' idx E Φ v :
  ICC_modality icd idx E 0 (Φ v 0) -∗ IC@{icd, idx} of_val v @ E {{ Φ }}.
Proof.
  rewrite ic_eq /ic_def.
  iIntros "H" (? ? ? ? [? [? ?]]%nsteps_val); simplify_eq.
  iIntros "Hi".
  iApply ICC_modality_intro.
  iApply (ICC_modality_mono with "[Hi] H"); simpl; auto.
  iIntros (?) "?"; iFrame.
Qed.

Lemma ic_strong_mono_Mod
      M idx `{!ICMIsInnerModal icd idx (λ E n P, M E P)%I}
      E1 E2 e Φ Ψ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  E1 ⊆ E2 → (∀ v n x, Φ v n x -∗ M E2 (Ψ v n x))
              ∗ IC@{icd, idx} e @ E1 {{ Φ }} ⊢ IC@{icd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (HM Hsb) "[Hi H]". rewrite ic_eq /ic_def.
  iIntros (σ1 σ2 v n) "Hr Ho".
  iSpecialize ("H" $! σ1 σ2 v n with "Hr Ho").
  iApply IC_modality_is_inner_modal.
  iApply (ICC_modality_mono with "[Hi] H"); first done.
  iIntros (x) "[HΦ Hsi]".
  iSpecialize ("Hi" with "HΦ").
  iApply (HM with "[Hsi]"); last done.
  by iIntros "?"; iFrame.
Qed.

Lemma ic_strong_mono_fupd
      `{!invG Σ} idx `{!ICMIsInnerModal icd idx (λ E n P, |={E}=> P)%I} E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  (∀ v n x, Φ v n x ={E2}=∗ Ψ v n x) ∗ IC@{icd, idx} e @ E1 {{ Φ }}
   ⊢ IC@{icd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply ic_strong_mono_Mod; eauto.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma ic_strong_mono_bupd
      idx `{!ICMIsInnerModal icd idx (λ E n P, |==> P)%I} E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v n x, Φ v n x ==∗ Ψ v n x)
              ∗ IC@{icd, idx} e @ E1 {{ Φ }} ⊢ IC@{icd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply ic_strong_mono_Mod; eauto.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma ic_strong_mono_wand idx E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  (∀ v n x, Φ v n x -∗ Ψ v n x) ∗ IC@{icd, idx} e @ E1 {{ Φ }}
  ⊢ IC@{icd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply (ic_strong_mono_Mod (λ _ P, P)); eauto.
  rewrite /ICMIsInnerModal; eauto.
Qed.

Lemma Mod_ic M idx `{!ICMIsOuterModal icd idx (λ E n P, M E P)%I} E e Φ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  (M E (IC@{icd, idx} e @ E {{ Φ }})) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  rewrite ic_eq /ic_def.
  iIntros (HM) "Hm".
  iIntros (σ1 σ2 v n) "% Ho".
  iApply IC_modality_is_outer_modal.
  iApply (HM with "[Ho]"); last done.
  iIntros "Hm". by iApply "Hm".
Qed.

Lemma ic_Mod M idx `{!ICMIsInnerModal icd idx (λ E n P, M E P)%I} E e Φ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  IC@{icd, idx} e @ E {{ v ; n | [x], M E (Φ v n x) }}
  ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros (HM) "H".
  iApply (ic_strong_mono_Mod _ idx E); try iFrame; auto.
  by iIntros (? ? ?) "H ?"; iApply (HM with "H").
Qed.

Lemma fupd_ic `{!invG Σ} idx
      `{!ICMIsOuterModal icd idx (λ E n P, |={E}=> P)%I}
 E e Φ : (|={E}=> IC@{icd, idx} e @ E {{ Φ }}) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_ic (λ E P, |={E}=> P))%I.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma ic_fupd
      `{!invG Σ} idx `{!ICMIsInnerModal icd idx (λ E n P, |={E}=> P)%I} E e Φ :
  IC@{icd, idx} e @ E {{ v; n | [x], |={E}=> Φ v n x }}
  ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (ic_strong_mono_fupd _ E); try iFrame; auto.
Qed.

Lemma bupd_ic idx
      `{!ICMIsOuterModal icd idx (λ E n P, |==> P)%I}
 E e Φ : (|==> IC@{icd, idx} e @ E {{ Φ }}) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_ic (λ E P, |==> P))%I.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma ic_bupd idx `{!ICMIsInnerModal icd idx (λ E n P, |==> P)%I} E e Φ :
  IC@{icd, idx} e @ E {{ v; n | [x], |==> Φ v n x }}
  ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (ic_strong_mono_bupd _ E); try iFrame; auto.
 Qed.

Lemma except_0_ic idx `{!ICMIsOuterModal icd idx (λ E n P, ◇ P)%I}
 E e Φ : (◇ IC@{icd, idx} e @ E {{ Φ }}) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_ic (λ E P, ◇ P))%I.
  by iIntros (? ? ?) "H >?"; iModIntro; iApply "H".
Qed.

Lemma ic_except_0 idx `{!ICMIsInnerModal icd idx (λ E n P, ◇ P)%I} E e Φ :
  IC@{icd, idx} e @ E {{ v; n | [x], ◇ Φ v n x }}
  ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (ic_strong_mono_Mod (λ E P, ◇ P)%I); eauto; last iFrame; auto.
  by iIntros (???) "H >?"; iModIntro; iApply "H".
Qed.

Lemma ic_bind K `{!LanguageCtx K} idx idx' f g E e Φ :
  ICC_modality_bind_condition icd idx idx' f g →
  IC@{icd, idx'} e @ E {{ v; m | [x],
      IC@{icd, f x} K (of_val v) @ E
        {{ w; n | [y], Φ w (m + n) (g x y) }} }}
  ⊢ IC@{icd, idx} K e @ E {{ Φ }}.
Proof.
  iIntros (Hcnd) "H".
  rewrite ic_eq /ic_def.
  iIntros (σ1 σ2 w n Hr) "Hsi".
  destruct (nsteps_bind _ Hr) as (k & σ' & u & Hle & Hstp1 & Hstp2).
  iSpecialize ("H" with "[] Hsi"); eauto.
  replace n with (k + (n - k)) by lia.
  iApply ICC_modality_bind; eauto.
  iApply (ICC_modality_mono); simpl; last done; first auto.
  iIntros (x) "[H Hsi]".
  iSpecialize ("H" with "[] Hsi"); by eauto.
Qed.

Lemma ic_atomic `{!invG Σ} idx `{!ICMSupportsAtomicShift icd idx}
      a E1 E2 e Φ `{!Atomic a e} :
  (|={E1,E2}=> IC@{icd, idx} e @ E2 {{ v; n | [x], |={E2,E1}=> Φ v n x }})
  ⊢ IC@{icd, idx} e @ E1 {{ Φ }}.
Proof.
  rewrite ic_eq /ic_def.
  iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
  pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
  iApply IC_supports_atomic_shift; eauto.
  iMod "H"; iModIntro.
  iSpecialize ("H" with "[] Ho"); eauto.
  iApply ICC_modality_mono; last done; auto.
  iIntros (?)  "[>H Hsi]".
  iModIntro; iFrame.
Qed.

Lemma ic_shift `{!invG Σ} idx `{!ICMAlwaysSupportsShift icd idx}
      E1 E2 e Φ :
  (|={E1,E2}=> IC@{icd, idx} e @ E2 {{ v; n | [x], |={E2,E1}=> Φ v n x }})
  ⊢ IC@{icd, idx} e @ E1 {{ Φ }}.
Proof.
  rewrite ic_eq /ic_def.
  iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
  iApply IC_always_supports_shift; eauto.
  iMod "H"; iModIntro.
  iSpecialize ("H" with "[] Ho"); eauto.
  iApply ICC_modality_mono; last done; auto.
  iIntros (?) "[>H Hsi]".
  iModIntro; iFrame.
Qed.

Lemma ic_change_of_index idx idx' f E e Φ :
  (∀ Ψ n, ICC_modality icd idx' E n (Ψ ∘ f) -∗ ICC_modality icd idx E n Ψ)
    -∗ IC@{icd, idx'} e @ E {{ λ v n x, Φ v n (f x)}}
  -∗ IC@{icd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "Hm H".
  rewrite ic_eq /ic_def.
  iIntros (σ1 σ2 v n Hr) "Hsi".
  iApply ("Hm").
  by iApply "H".
Qed.

(** * Derived rules *)
Lemma ic_mono idx E e Φ Ψ : (∀ v n x, Φ v n x ⊢ Ψ v n x) →
  IC@{icd, idx} e @ E {{ Φ }} ⊢ IC@{icd, idx} e @ E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H". iApply ic_strong_mono_wand; eauto.
  iFrame.
  by iIntros (v n x); iApply HΦ.
Qed.
Lemma ic_mask_mono idx E1 E2 e Φ : E1 ⊆ E2 →
  IC@{icd, idx} e @ E1 {{ Φ }} ⊢ IC@{icd, idx} e @ E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ic_strong_mono_wand); eauto; iFrame; eauto. Qed.
Global Instance ic_mono' idx E e :
  Proper (pointwise_relation
            _ (pointwise_relation _ (pointwise_relation _ (⊢))) ==> (⊢))
         ( @ic Λ Σ icd _ idx E e).
Proof. intros ???. by apply ic_mono => ???; apply H. Qed.

Lemma ic_value idx E Φ e v :
  IntoVal e v →
  ICC_modality icd idx E 0 (Φ v 0) ⊢ IC@{icd, idx} e @ E {{ Φ }}.
Proof. intros <-. by rewrite ic_value'. Qed.

Lemma ic_frame_l idx E e Φ R :
  R ∗ IC@{icd, idx} e @ E {{ Φ }} ⊢ IC@{icd, idx} e @ E {{ v; n | [x], R ∗ Φ v n x }}.
Proof.
  iIntros "[??]".
  iApply (ic_strong_mono_wand _ _ _ _ Φ); try iFrame; eauto.
Qed.
Lemma ic_frame_r idx E e Φ R :
  IC@{icd, idx} e @ E {{ Φ }} ∗ R ⊢ IC@{icd, idx} e @ E {{ v; n | [x], Φ v n x ∗ R }}.
Proof.
  iIntros "[??]".
  iApply (ic_strong_mono_wand _ _ _ _ Φ); try iFrame; eauto.
Qed.

Lemma ic_wand_l idx E e Φ Ψ :
  (∀ v n x, Φ v n x -∗ Ψ v n x) ∗
  IC@{icd, idx} e @ E {{ Φ }} ⊢ IC@{icd, idx} e @ E {{ Ψ }}.
Proof.
  iIntros "[H Hic]". iApply (ic_strong_mono_wand _ E); auto.
  iFrame "Hic". iIntros (???) "?". by iApply "H".
Qed.
Lemma ic_wand_r idx E e Φ Ψ :
  IC@{icd, idx} e @ E {{ Φ }} ∗
  (∀ v n x, Φ v n x -∗ Ψ v n x)
  ⊢ IC@{icd, idx} e @ E {{ Ψ }}.
Proof. by rewrite comm ic_wand_l. Qed.
End ic.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {Λ Σ} (icd : ICData Λ Σ) `{!ICC icd}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → nat → ICC_Extra → iProp Σ.

  Global Instance frame_ic p idx E e R Φ Ψ :
    (∀ v n x, Frame p R (Φ v n x) (Ψ v n x)) →
    Frame p R (IC@{icd, idx} e @ E {{ Φ }}) (IC@{icd, idx} e @ E {{ Ψ }}).
  Proof.
    rewrite /Frame=> HR.
    rewrite ic_frame_l.
    apply ic_mono.
    apply HR.
  Qed.

  Global Instance is_except_0_ic idx `{!ICMIsOuterModal icd idx (λ E n P, ◇ P)%I}
         E e Φ : IsExcept0 (IC@{icd, idx} e @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 ic_eq /ic_def.
    iIntros "H".
    iIntros (σ1 σ2 v n Hrd) "Ho".
    iApply IC_modality_is_outer_modal.
    iMod "H"; iModIntro.
    by iApply "H".
  Qed.

  Global Instance elim_modal_bupd_ic idx
         `{!ICMIsOuterModal icd idx (λ E n P, |==> P)%I} p E e P Φ :
    ElimModal True p false (|==> P) P (IC@{icd, idx} e @ E {{ Φ }})
              (IC@{icd, idx} e @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /=.
    iIntros (_) "[H1 H2]".
    rewrite ic_eq /ic_def.
    iIntros (σ1 σ2 v n Hrd) "Ho".
    iApply IC_modality_is_outer_modal.
    iMod "H1". iModIntro.
    by iApply ("H2" with "H1").
  Qed.

  Global Instance elim_modal_fupd_ic
        `{invG Σ} `{!ICMIsOuterModal icd idx (λ E n P, |={E}=> P)%I} p E e P Φ :
    ElimModal True p false (|={E}=> P) P (IC@{icd, idx} e @ E {{ Φ }})
              (IC@{icd, idx} e @ E {{ Φ }}).
  Proof.
      by rewrite /ElimModal intuitionistically_if_elim /=
                 fupd_frame_r wand_elim_r fupd_ic.
  Qed.

End proofmode_classes.
