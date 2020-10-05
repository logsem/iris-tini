From Autosubst Require Export Autosubst.
From logrel_ifc.lambda_sec Require Export lang lattice.

Section syntactic_flowsto.

  Inductive label_term `{SecurityLattice label} :=
  | LVar (x : var)
  | LJoin (l l' : label_term)
  | LLabel (ℓ : label).

  Context `{SecurityLattice label}.

  Global Instance label_term_ids : Ids label_term . Proof. derive. Defined.
  Global Instance label_term_rename : Rename label_term . Proof. derive. Defined.
  Global Instance label_term_subst : Subst label_term . Proof. derive. Defined.
  Global Instance label_term_substlemmas : SubstLemmas label_term . derive. Defined.

  Inductive flowsto : label_term → label_term  → Prop :=
  | FRefl l :
      flowsto l l
  | FTrans l1 l2 l3 :
      flowsto l1 l2 →
      flowsto l2 l3 →
      flowsto l1 l3
  | FBottom l :
      flowsto (LLabel ⊥) l
  | FTop l :
      flowsto l (LLabel ⊤)
  | FLabel ℓ1 ℓ2 :
      ℓ1 ⊑ ℓ2 →
      flowsto (LLabel ℓ1) (LLabel ℓ2)
  | FJoin l1 l2 l3 :
      flowsto l1 l3 →
      flowsto l2 l3 →
      flowsto (LJoin l1 l2) l3.

  Global Instance flowsto_refl : Reflexive flowsto.
  Proof. by constructor. Qed.

  Global Instance flowsto_trans : Transitive flowsto.
  Proof. by econstructor. Qed.

End syntactic_flowsto.

Notation "a ⊑ₛ b" := (flowsto a b) (at level 70) : stdpp_scope.
Infix "⊔ₛ" := (LJoin) (at level 50) : stdpp_scope.
Notation "⊥ₛ" := (LLabel bot) : stdpp_scope.
Notation "⊤ₛ" := (LLabel top) : stdpp_scope.

Hint Constructors flowsto : core.

Section lambda_sec_types.
  Context `{SecurityLattice label}.

  Inductive type :=
  | TUnit
  | TBool
  | TNat
  | TVar (x : var)
  | TRef (τ : sectype)
  | TArrow (ℓₑ : label_term) (τ1 τ2 : sectype)
  | TProd (τ1 τ2 : sectype)
  | TSum (τ1 τ2 : sectype)
  | TForall (ℓₑ : label_term) (τ : sectype)
  | TLForall (ℓₑ : label_term) (τ : sectype)
  | TExist (τ : sectype)
  | TRec (τ : sectype)
  with sectype :=
  | TSec (ℓ : label_term) (t : type).

  Implicit Types t : type.
  Implicit Types τ : sectype.

  (* generate mutual induction principles *)
  Scheme type_mut := Induction for type Sort Prop
    with sectype_mut := Induction for sectype Sort Prop.

  Notation "t @ ℓ" := (TSec ℓ t) (at level 40).

  (* -------------------- autosubst lemmas -------------------- *)

  Global Instance Ids_type : Ids type. derive. Defined.
  Global Instance Ids_sectype : Ids sectype := λ n, TSec ⊥ₛ TUnit.

  Fixpoint hsubst_label_type (sigma : var → label_term) (t : type) : type :=
    let _ := hsubst_label_sectype : HSubst label_term sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => TVar x
    | TRef τ => TRef (hsubst sigma τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ'.[sigma] (hsubst sigma τ1) (hsubst sigma τ2)
    | TProd τ1 τ2 => TProd (hsubst sigma τ1) (hsubst sigma τ2)
    | TSum τ1 τ2 => TSum (hsubst sigma τ1) (hsubst sigma τ2)
    | TForall ℓ τ => TForall ℓ.[sigma] (hsubst sigma τ)
    | TLForall ℓ τ => TLForall ℓ.[up sigma] (hsubst (up sigma) τ)
    | TExist τ => TExist (hsubst sigma τ)
    | TRec τ => TRec (hsubst sigma τ)
    end
  with hsubst_label_sectype (sigma : var → label_term) (τ : sectype) : sectype :=
    let _ := hsubst_label_type : HSubst label_term type in
    match τ with
    | t @ ℓ => (hsubst sigma t) @ ℓ.[sigma]
    end.

  Global Instance HSubst_label_type : HSubst label_term type := hsubst_label_type.
  Global Instance HSubst_label_sectype : HSubst label_term sectype := hsubst_label_sectype.

  Local Lemma hsubst_label_type_id (t : type) : t.|[ids] = t
  with hsubst_label_sectype_id (τ : sectype) : τ.|[ids] = τ.
  Proof.
    - destruct t; rewrite /= ?up_id ?subst_id ?hsubst_label_sectype_id //.
    - destruct τ; rewrite /= hsubst_label_type_id subst_id //.
  Qed.

  Local Lemma hsubst_label_type_comp (theta eta : var → label_term) (t : type) :
    t.|[theta].|[eta] = t.|[theta >> eta]
  with hsubst_label_sectype_comp (theta eta : var → label_term) (τ : sectype) :
    τ.|[theta].|[eta] = τ.|[theta >> eta].
  Proof.
    - destruct t; rewrite /= ?subst_comp ?hsubst_label_sectype_comp ?up_comp //.
    - destruct τ; rewrite /= hsubst_label_type_comp subst_comp //.
  Qed.

  Global Instance HSubstLemmas_label_type : HSubstLemmas label_term type.
  Proof.
    split.
    - apply hsubst_label_type_id.
    - by simpl.
    - apply hsubst_label_type_comp.
  Qed.

  Global Instance HSubstLemmas_label_sectype : HSubstLemmas label_term sectype.
  Proof.
    split.
    - apply hsubst_label_sectype_id.
    - by intros; simpl.
    - apply hsubst_label_sectype_comp.
  Qed.

  Fixpoint rename_type (xi : var → var) (t : type) : type :=
    let _ := rename_sectype : Rename sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => TVar (xi x)
    | TRef τ => TRef (rename xi τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ' (rename xi τ1) (rename xi τ2)
    | TProd τ1 τ2 => TProd (rename xi τ1) (rename xi τ2)
    | TSum τ1 τ2 => TSum (rename xi τ1) (rename xi τ2)
    | TForall ℓ τ => TForall ℓ (rename (upren xi) τ)
    | TLForall ℓ τ => TLForall ℓ (rename xi τ)
    | TExist τ => TExist (rename (upren xi) τ)
    | TRec τ => TRec (rename (upren xi) τ)
    end
  with rename_sectype (xi : var → var) (τ : sectype) : sectype :=
    let _ := rename_type : Rename type in
    match τ with
    | t @ ℓ => (rename xi t) @ ℓ
    end.

  Global Instance Rename_type : Rename type := rename_type.
  Global Instance Rename_sectype : Rename sectype := rename_sectype.

  Fixpoint subst_type (sigma : var → type) (t : type) : type :=
    let _ := hsubst_sectype : HSubst type sectype in
    match t with
    | TUnit
    | TBool | TNat => t
    | TVar x => sigma x
    | TRef τ => TRef (hsubst sigma τ)
    | TArrow ℓ' τ1 τ2 => TArrow ℓ' (hsubst sigma τ1) (hsubst sigma τ2)
    | TProd τ1 τ2 => TProd (hsubst sigma τ1) (hsubst sigma τ2)
    | TSum τ1 τ2 => TSum (hsubst sigma τ1) (hsubst sigma τ2)
    | TForall ℓ τ => TForall ℓ (hsubst (up sigma) τ)
    | TLForall ℓ τ => TLForall ℓ (hsubst (sigma >>| ren (+1)) τ)
    | TExist τ => TExist (hsubst (up sigma) τ)
    | TRec τ => TRec (hsubst (up sigma) τ)
    end
  with hsubst_sectype (sigma : var → type) (τ : sectype) : sectype :=
    let _ := subst_type : Subst type in
    match τ with
    | t @ ℓ => (subst sigma t) @ ℓ
    end.

  Global Instance Subst_type : Subst type := subst_type.
  Global Instance HSubst_type : HSubst type sectype := hsubst_sectype.

  Local Lemma ren_label_subst_type xi (sigma : var → type) n :
    (xi >>> (λ x : var, (sigma x).|[@ren label_term _ (+n)])
     = λ x : var, (sigma (xi x)).|[@ren label_term _ (+n)]).
  Proof.
    apply FunctionalExtensionality.functional_extensionality; by intros x; asimpl.
  Qed.

  Local Lemma rename_subst_comp_type xi sigma t :
    (rename xi t).[sigma] = t.[xi >>> sigma]
  with rename_hsubst_sectype_comp xi sigma τ :
    (rename xi τ).|[sigma] = τ.|[xi >>> sigma].
  Proof.
    - destruct t;
        repeat (match goal with τ : sectype |- _ => destruct τ end);
        rewrite /= ?rename_subst_comp_type // up_comp_ren_subst //.      
    - by destruct τ; simpl; f_equal.
  Qed.

  Local Lemma rename_subst_ren xi t : rename xi t = t.[ren xi]
  with rename_hsubst_ren xi τ : rename xi τ = τ.|[ren xi].
  Proof.
    - destruct t; 
        repeat (match goal with τ : sectype |- _ => destruct τ end); 
        rewrite /= ?rename_subst_ren // up_upren_internal //.
    - by destruct τ; simpl; f_equal.
  Qed.

  Local Lemma rename_subst_subst_comp xi sigma t :
    (rename xi t).[sigma] = t.[xi >>> sigma]
  with rename_hsubst_secsubst_comp xi sigma τ :
    (rename xi τ).|[sigma] = τ.|[xi >>> sigma].
  Proof.
    - destruct t; simpl;
        repeat (match goal with τ : sectype |- _ => destruct τ end); simpl;
          rewrite ?rename_subst_subst_comp // up_comp_ren_subst //.
    - by destruct τ; simpl; f_equal.
  Qed.

  Local Lemma rename_type_label_subst_commute xi t s :
    rename xi t.|[s] = (rename xi t).|[s].
  Proof.
    move: xi s. refine ((fix f t xi s {struct t} := _) t).
    destruct t;
      repeat (match goal with τ : sectype |- _ => destruct τ end);
      simpl; rewrite ?f //.
  Qed.

  Local Lemma rename_type_ren_label xi (sigma : var → type) :
    (λ x : var, (sigma x).|[ren (+1)]) >>> rename xi
    = sigma >>> rename xi >>| ren (+1).
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    intros. asimpl. apply rename_type_label_subst_commute.
  Qed.

  Local Lemma rename_subst_comp_type_rename sigma xi t :
    rename xi t.[sigma] = t.[sigma >>> rename xi]
  with rename_hsubst_sectype_comp_rename sigma xi τ :
    rename xi τ.|[sigma] = τ.|[sigma >>> rename xi].
  Proof.
    - destruct t; simpl;
        repeat (match goal with τ : sectype |- _ => destruct τ end);
        simpl; try rewrite ?rename_subst_comp_type_rename //.
      + repeat f_equal. rewrite up_comp_subst_ren_internal //.
        * apply rename_subst_ren.
        * apply rename_subst_subst_comp.
      + rewrite rename_type_ren_label //.
      + repeat f_equal. rewrite up_comp_subst_ren_internal //.
        * apply rename_subst_ren.
        * apply rename_subst_subst_comp.
      + repeat f_equal. rewrite up_comp_subst_ren_internal //.
        * apply rename_subst_ren.
        * apply rename_subst_subst_comp.
    - by destruct τ; simpl; f_equal.
  Qed.

  Lemma rename_subst xi t : rename xi t = t.[ren xi]
  with rename_hsubst xi τ : rename xi τ = τ.|[ren xi].
  Proof.
    - destruct t; simpl; rewrite ?rename_hsubst //; f_equal; autosubst.     
    - by destruct τ; simpl; f_equal.
  Qed.

  Lemma subst_type_id t : t.[ids] = t
  with hsubst_id τ : τ.|[ids] = τ.
  Proof.
    - assert (up_id : up ids = ids :> (var → type))
        by (apply up_id_internal; reflexivity).
      destruct t; simpl;
        repeat (match goal with τ : sectype |- _ => destruct τ end);
        simpl; rewrite ?up_id ?subst_type_id //. 
    - by destruct τ; simpl; f_equal.
  Qed.

  Lemma up_hcomp_dist (sigma : var → type) theta :
    up (sigma >>| theta) = up sigma >>| theta.
  Proof.
    rewrite up_hcomp_internal //; auto using rename_type_label_subst_commute.
  Qed.

  Lemma upn_hsubst_ren n t :
    upn n (t .: ids) >>| ren (+1) = upn n (t.|[ren (+1)] .: ids).
  Proof.
    by rewrite -up_hcomp_n_internal; [|apply up_hcomp_dist]; asimpl.
  Qed.

  Lemma hsubst_label_subst_type_commute t tau sigma :
    t.|[sigma].[tau >>| sigma] = t.[tau].|[sigma].
  Proof.
    move: sigma tau. refine ((fix IH t sigma tau {struct t} := _) t).
    destruct t;
      repeat (match goal with τ : sectype |- _ => destruct τ end);
      simpl; try rewrite ?IH //; do 2 f_equal; rewrite ?up_hcomp_dist //.
    move: IH => /(_ t (up sigma) (tau >>| ren (+1))). by asimpl.
  Qed.

  Lemma hsubst_type_label_subst_commute (sigma tau : var → type) σ:
    sigma >>| σ >> (tau >>| σ) = sigma >> tau >>| σ.
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    intros ?. asimpl. apply hsubst_label_subst_type_commute.
  Qed.

  Lemma subst_type_comp sigma tau t : t.[sigma].[tau] = t.[sigma >> tau]
  with hsubst_comp sigma tau τ : τ.|[sigma].|[tau] = τ.|[sigma >> tau].
  Proof.
    - destruct t; simpl;
        (repeat (match goal with τ : sectype |- _ => destruct τ end));
        simpl; rewrite ?subst_type_comp //.      
      + rewrite  up_comp_internal; [done|done|..].
        * apply rename_subst_comp_type.
        * apply rename_subst_comp_type_rename.
      + rewrite hsubst_type_label_subst_commute //.
      + rewrite up_comp_internal; [done|done|..].
        * apply rename_subst_comp_type.
        * apply rename_subst_comp_type_rename.
      + rewrite up_comp_internal; [done|done|..].
        * apply rename_subst_comp_type.
        * apply rename_subst_comp_type_rename.
    - by destruct τ; simpl; f_equal.
  Qed.

  Global Instance SubstLemmas_type : SubstLemmas type.
  Proof.
    constructor; try done.
    - apply rename_subst.
    - apply subst_type_id.
    - apply subst_type_comp.
  Qed.

  Global Instance HSubstLemmas_sectype_type : HSubstLemmas type sectype.
  Proof.
    constructor; try done.
    - apply hsubst_id.
    - apply hsubst_comp.
  Qed.

  (* -------------------- /autosubst lemmas -------------------- *)

End lambda_sec_types.

Notation "τ @ ℓ" := (TSec ℓ τ) (at level 60).
