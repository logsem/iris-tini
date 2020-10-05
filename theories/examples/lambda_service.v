From iris.proofmode Require Import tactics.
From mwp.mwp_modalities Require Import mwp_step_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right ni_logrel_lemmas.
From logrel_ifc.lambda_sec Require Export lattice fundamental_binary notation.

Instance tpSecurityLattice : SecurityLattice tplabel := { ζ := L }.
Notation H := (LLabel H).
Notation L := (LLabel L).

(* This example showcases the interesting bit of an Amazon "lambda-service"
   where untrusted users have lambdas that may depend on some secrets (keys,
   environment variables, etc) and the functions get called sequentially.

   In a *termination-sensitive* setting, this example would not be
   noninterferent as [f] may leak secrets through termination. *)

(* f secret1 ;; g secret2 *)
Definition lambda_service : expr := (($1 $0) ;; ($3 $2))%E.

(* both fuctions take some (possibly secret) input and can make arbitrary side
   effects (e.g. writing the input to a ref with secret content) *)
Definition f_type τ := (TArrow L τ (TBool @ L)) @ L.

Section typed.

  Lemma lambda_typed τ1 τ2 :
    [τ1; f_type τ1; τ2; f_type τ2] # L ⊢ₜ lambda_service : TBool @ L.
  Proof.
    eapply Seq_typed.
    - eapply App_typed.
      + by apply Var_typed.
      + by apply Var_typed.
      + simpl. reflexivity.
      + by constructor.
    - eapply App_typed.
      + by apply Var_typed.
      + by apply Var_typed.
      + simpl. reflexivity.
      + by constructor.
  Qed.

End typed.
