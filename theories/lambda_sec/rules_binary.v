From iris.algebra Require Import list.
From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From mwp.prelude Require Export base.
From mwp Require Export mwp mwp_triple.
From mwp.mwp_modalities.ni_logrel Require Export mwp_right mwp_left.
From logrel_ifc.lambda_sec Require Export lang lattice rules_unary logrel_unary.

Class secG Σ := SecG {
  secG_invG :> invG Σ;
  secG_gen_heapG_left  :> gen_heapG loc val Σ;
  secG_gen_heapG_right :> gen_heapG loc val Σ;
}.

(** left and right heap *)
Definition mapsto_left `{secG Σ} (l : loc) (q : dfrac) (v : val) :=
  @mapsto loc _ _ val Σ secG_gen_heapG_left l q v.
Definition mapsto_right `{secG Σ} (l : loc) (q : dfrac) (v : val) :=
  @mapsto loc _ _ val Σ secG_gen_heapG_right l q v.

Definition gen_heap_interp_left `{secG Σ} (σ : gmap loc val) :=
  @gen_heap_interp _ _ _ _ _ secG_gen_heapG_left σ.

Definition gen_heap_interp_right `{secG Σ} (σ : gmap loc val) :=
  @gen_heap_interp _ _ _ _ _ secG_gen_heapG_right σ.

Notation "l ↦ₗ{ dq } v" := (mapsto_left l dq v%V)
  (at level 20, dq at level 50, format "l  ↦ₗ{ dq }  v") : bi_scope.
Notation "l ↦ₗ{# q } v" := (mapsto_left l (DfracOwn q) v%V)
  (at level 20, format "l  ↦ₗ{# q }  v") : bi_scope.
Notation "l ↦ₗ v" := (mapsto_left  l (DfracOwn 1) v%V)
  (at level 20) : bi_scope.

Notation "l ↦ᵣ{ dq } v" := (mapsto_right l dq v%V)
  (at level 20, dq at level 50, format "l  ↦ᵣ{ dq }  v") : bi_scope.
Notation "l ↦ᵣ{# q } v" := (mapsto_right l (DfracOwn q) v%V)
  (at level 20, format "l  ↦ᵣ{# q }  v") : bi_scope.
Notation "l ↦ᵣ v" :=
  (mapsto_right l (DfracOwn 1) v%V) (at level 20) : bi_scope.

(** unary interpretations with left and right heaps *)
Section left_right.
  Context `{secG Σ}.
  Context `{SecurityLattice label}.

  Notation D := (val -d> iPropO Σ).
  Notation lty := (listO D -n> listO labelO -d> D).

  Definition secG_un_left : secG_un Σ :=
    SecG_un _ _ secG_gen_heapG_left.
  Definition secG_un_right : secG_un Σ :=
    SecG_un _ _ secG_gen_heapG_right.

  Definition interp_un_left t : lty :=
    (@interp_un _ secG_un_left _ _ t).
  Definition interp_un_sec_left τ : lty :=
    (@interp_un_sec _ secG_un_left _ _ τ).

  Definition interp_un_expr_left τ  :=
    (@interp_un_expr _ secG_un_left _ _ (interp_un_sec_left τ)).
  Definition interp_un_env_left :=
    (@interp_un_env _ secG_un_left _ _).

  Definition interp_un_right t : lty :=
    (@interp_un _ secG_un_right _ _ t).
  Definition interp_un_sec_right τ : lty :=
    (@interp_un_sec _ secG_un_right _ _ τ).

  Definition interp_un_expr_right τ :=
    (@interp_un_expr _ secG_un_right _ _ (interp_un_sec_right τ)).
  Definition interp_un_env_right :=
    (@interp_un_env _ secG_un_right _ _).
End left_right.

Global Arguments secG_un_left : simpl never.
Global Arguments secG_un_right : simpl never.
Global Arguments interp_un_left : simpl never .
Global Arguments interp_un_sec_left : simpl never.
Global Arguments interp_un_right : simpl never.
Global Arguments interp_un_sec_right : simpl never.

Notation "⌊ τ ₗ⌋ₛ" := (interp_un_sec_left τ) (at level 0, τ at level 70).
Notation "⌊ τ ₗ⌋" := (interp_un_left τ) (at level 0, τ at level 70).

Notation "⌊ τ ₗ⌋ₑ" := (interp_un_expr_left τ) (at level 0, τ at level 70).
Notation "⌊ Γ ₗ⌋*" := (interp_un_env_left Γ) (at level 0, Γ at level 70).

Notation "⌊ τ ᵣ⌋ₛ" := (interp_un_sec_right τ) (at level 0, τ at level 70).
Notation "⌊ τ ᵣ⌋" := (interp_un_right τ) (at level 0, τ at level 70).

Notation "⌊ τ ᵣ⌋ₑ" := (interp_un_expr_right τ) (at level 0, τ at level 70).
Notation "⌊ Γ ᵣ⌋*" := (interp_un_env_right Γ) (at level 0, Γ at level 70).

Section mwp_binary.
  Context `{!secG Σ}.

  Definition SI_left  (σ : state) : iProp Σ := (gen_heap_interp_left σ)%I.
  Definition SI_right (σ : state) : iProp Σ := (gen_heap_interp_right σ)%I.

  Definition mwp_binary := mwpd_left SI_left SI_right.
  Definition mwp_right := mwpd_right SI_right.

End mwp_binary.
