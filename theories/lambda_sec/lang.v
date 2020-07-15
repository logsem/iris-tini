From iris.program_logic Require Export language ectx_language ectxi_language.
From logrel_ifc.prelude Require Export base.
From stdpp Require Import gmap.

Module lambda_sec.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Definition loc := positive.

  Inductive expr :=
  | Var (x : var)
  | Lam (e : {bind expr})
  | App (e1 e2 : expr)
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)
  (* Base types *)
  | Unit
  | Bool (b : bool)
  | Nat (n : nat)
  | BinOp (op : binop) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Proj1 (e : expr)
  | Proj2 (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 e2 : {bind expr})
  (* References *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Store (e1 e2 : expr)
  | Load (e : expr)
  (* Type polymorphism *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Label polymorphism *)
  | TLLam (e : expr)
  | TLApp (e : expr)
  (* Existentials *)
  | Pack (e : expr)
  | Unpack (e1 : expr) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  .

  Instance Ids_expr : Ids expr. derive. Defined.
  Instance Rename_expr : Rename expr. derive. Defined.
  Instance Subst_expr : Subst expr. derive. Defined.
  Instance SubstLemmas_expr : SubstLemmas expr. derive. Defined.

  Global Instance expr_inh : Inhabited expr.
  Proof. repeat constructor. Qed.

  Inductive val :=
  | UnitV
  | BoolV (b : bool)
  | NatV (n : nat)
  | LamV (e : expr)
  | TLamV (e : expr)
  | TLLamV (e : expr)
  | PairV (l r: val)
  | InjLV (v: val)
  | InjRV (v: val)
  | LocV (l : loc)
  | FoldV (v : val)
  | PackV (v : val).

  Global Instance val_inh : Inhabited val.
  Proof. repeat constructor. Qed.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | UnitV => Unit
    | BoolV b => Bool b
    | NatV n => Nat n
    | LamV e => Lam e
    | TLamV e => TLam e
    | TLLamV e => TLLam e
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | LocV l => Loc l
    | FoldV v => Fold (of_val v)
    | PackV v => Pack (of_val v)
    end.

  Notation "# v" := (of_val v) (at level 20).

  Fixpoint binop_eval (op : binop) (a b : nat) : val :=
    match op with
    | Add => NatV (a + b)
    | Sub => NatV (a - b)
    | Mult => NatV (a * b)
    | Eq => BoolV $ bool_decide (a = b)
    | Le => BoolV $ bool_decide (a ≤ b)
    | Lt => BoolV $ bool_decide (a < b)
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Unit => Some UnitV
    | Bool b => Some $ BoolV b
    | Nat n => Some $ NatV n
    | Lam e => Some $ LamV e
    | TLam e => Some $ TLamV e
    | TLLam e => Some $ TLLamV e
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some $ PairV v1 v2
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Loc l => Some $ LocV l
    | Fold e => v ← to_val e; Some (FoldV v)
    | Pack e => v ← to_val e; Some (PackV v)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | TLAppCtx
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | InjLCtx | InjRCtx
  | Proj1Ctx | Proj2Ctx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | AllocCtx | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | FoldCtx
  | UnfoldCtx
  | PackCtx
  | UnpackCtx (e : expr)
  .

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (# v1) e
    | LetInCtx e2 => LetIn e e2
    | SeqCtx e2 => Seq e e2
    | TAppCtx => TApp e
    | TLAppCtx => TLApp e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (# v1) e
    | IfCtx e1 e2 => If e e1 e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (# v1) e
    | InjLCtx => InjL e | InjRCtx => InjR e
    | Proj1Ctx => Proj1 e | Proj2Ctx => Proj2 e
    | CaseCtx e1 e2 => Case e e1 e2
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (# v1) e
    | FoldCtx => Fold e
    | UnfoldCtx => Unfold e
    | PackCtx => Pack e
    | UnpackCtx e' => Unpack e e'
    end.

  Definition state : Type := gmap loc val.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* Lam β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
  (* TLam β *)
  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []
  (* LetIn-β *)
  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []
  (* Seq-β *)
  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []
  (* TLLam β *)
  | LBeta e σ :
      head_step (TLApp (TLLam e)) σ [] e σ []
  (* BinOp *)
  | BinOpS op n1 n2 σ :
      head_step (BinOp op (Nat n1) (Nat n2)) σ [] (# (binop_eval op n1 n2)) σ []
  (* If Then Else *)
  | IfFalseS e1 e2 σ :
      head_step (If (Bool false) e1 e2) σ [] e2 σ []
  | IfTrueS e1 e2 σ :
      head_step (If (Bool true) e1 e2) σ [] e1 σ []
  (* Products *)
  | Proj1S e1 e2 v1 v2 σ :
      to_val e1 = Some v1 →
      to_val e2 = Some v2 →
      head_step (Proj1 $ Pair e1 e2) σ [] (of_val v1) σ []
  | Proj2S e1 e2 v1 v2 σ :
      to_val e1 = Some v1 →
      to_val e2 = Some v2 →
      head_step (Proj2 $ Pair e1 e2) σ [] (of_val v2) σ []
  (* Sums *)
  | CaseLS e0 e1 e2 v0 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] (e1.[e0/]) σ []
  | CaseRS e0 e1 e2 v0 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] (e2.[e0/]) σ []
  (* References *)
  | AllocS e v l σ :
      to_val e = Some v →
      σ !! l = None →
      head_step (Alloc e) σ [] (Loc l) (<[l := v]>σ) []
  | StoreS e v l σ :
      to_val e = Some v →
      is_Some $ σ !! l →
      head_step (Store (Loc l) e) σ [] Unit (<[l := v]>σ) []
  | LoadS l v σ :
      σ !! l = Some v →
      head_step (Load $ Loc l) σ [] (of_val v) σ []
  (* Existentials *)
  | UnpackPackS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      head_step (Unpack (Pack e1) e2) σ [] (e2.[e1/]) σ []
  (* Recursive Types *)
  | UnfoldFoldS e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []
  .

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal;
    repeat match goal with | H: context[to_val ?e] |- _  => destruct (to_val e) end;
    match goal with | H: _ = Some _ |- _ => inversion H end; simpl;
      repeat match goal with | H: context[ # _ = _ ] |- _ => rewrite H; [eauto | done] end.
  Qed.

  Lemma loc_to_val l : Loc l = # (LocV l).
  Proof. reflexivity. Qed.

  Lemma bool_to_val b : Bool b = # (BoolV b).
  Proof. reflexivity. Qed.

  Lemma nat_to_val n : Nat n = # (NatV n).
  Proof. reflexivity. Qed.

  Lemma lam_to_val e : Lam e = # (LamV e).
  Proof. reflexivity. Qed.

  Lemma pair_to_val v1 v2 :
    Pair (#v1) (#v2) = # (PairV v1 v2).
  Proof. done. Qed.

  Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v H]. destruct Ki; simplify_option_eq;
         repeat match goal with | H: context[to_val ?e] |- _  => destruct (to_val e) end;
         simplify_eq; eauto.
  Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 e2 σ2 ef κ :
    head_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef κ :
    head_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
      repeat match goal with
             | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
             end; auto.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) σ) in
    to_val e = Some v → head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) [].
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 efs κ : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.
End lambda_sec.

(** Language *)
Canonical Structure lambda_sec_ectxi_lang := EctxiLanguage lambda_sec.lang_mixin.
Canonical Structure lambda_sec_ectx_lang := EctxLanguageOfEctxi lambda_sec_ectxi_lang.
Canonical Structure lambda_sec_lang := LanguageOfEctx lambda_sec_ectx_lang.

Export lambda_sec.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.
Global Instance is_atomic_correct s e : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic,  ectx_language_atomic.
  - destruct 1; simpl in *; try tauto; eauto.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.
Hint Resolve to_of_val : core.
