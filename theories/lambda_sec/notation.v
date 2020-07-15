From iris.program_logic Require Import language.
From logrel_ifc.lambda_sec Require Export lang types.
Set Default Proof Using "Type".

(* Terms *)
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Coercion App : expr >-> Funclass.

Coercion Nat : nat >-> expr.
Coercion Bool : bool >-> expr.
Coercion NatV : nat >-> val.
Coercion BoolV : bool >-> val.
Coercion LocV : loc >-> val.

Notation "'match:' e0 'with' 'InjL' => e1 | 'InjR' => e2 'end'" :=
  (Case e0 e1 e2)
  (e0, e1, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  =>  '/  ' e1 ']'  '/' '[' |  'InjR'   =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' => e1 | 'InjL' => e2 'end'" :=
  (Case e0 e2 e1)
  (e0, e1, e2 at level 200, only parsing) : expr_scope.

Notation "$ x" := (Var x)
  (at level 9,
   format "$ x") : expr_scope.

Notation "λ: e" := (Lam e%E)
  (at level 200, e at level 200,
   format "'[' 'λ:'  e  ']'") : expr_scope.

Notation "λ: e" := (LamV e%E)
  (at level 200, e at level 200,
   format "'[' 'λ:'  e  ']'") : val_scope.

Notation "Λₜ: e" := (TLam e%E)
  (at level 200, e at level 200,
   format "'[' 'Λₜ:' e ']'") : expr_scope.
Notation "Λₜ: e" := (TLamV e%E)
  (at level 200, e at level 200,
   format "'[' 'Λₜ:'  e  ']'") : val_scope.

Notation "Λₗ: e" := (TLLam e%E)
  (at level 200, e at level 200,
   format "'[' 'Λₗ:'  e  ']'") : expr_scope.
Notation "Λₗ: e" := (TLLamV e%E)
  (at level 200, e at level 200,
   format "'[' 'Λₗ:'  e  ']'") : val_scope.

Notation "e '<_>ₜ'" := (TApp e%E) (at level 10, only parsing) : expr_scope.
Notation "e '<_>ₗ'" := (TLApp e%E) (at level 10, only parsing) : expr_scope.

Notation "'pack:' e" := (Pack e%E)
  (at level 200, e at level 200,
   format "'[' 'pack:'  e ']'") : expr_scope.

Notation "'unpack:' e1 'in' e2" := (Unpack e1%E e2%E)
  (at level 200, e1, e2 at level 200,
   format "'[' 'unpack:'  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "'unpack:' e1 'in' e2" := (Unpack e1%E e2%E)
  (at level 200, e1, e2 at level 200,
   format "'[' 'unpack:'  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

Notation "'let:' e1 'in' e2" := (LetIn e1%E e2%E)
  (at level 200, e1, e2 at level 200,
   format "'[' 'let:'  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Seq e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

Notation "()" := Unit : val_scope.
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E) (at level 10) : expr_scope.

Notation "e1 + e2" := (BinOp Add e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp Sub e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp Mult e1%E e2%E) : expr_scope.

Notation "e1 ≤ e2" := (BinOp Le e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp Lt e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp Eq e1%E e2%E) : expr_scope.

Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(* Types *)
Bind Scope ty_scope with type.
Delimit Scope ty_scope with type.

Bind Scope lbl_scope with label_term.
Delimit Scope lbl_scope with label_term.

Notation "$ x" := (TVar x) (at level 9, format "$ x"): ty_scope.
Notation "§ x" := (LVar x) (at level 9, format "§ x") : lbl_scope.
Notation "()" := TUnit : ty_scope.
Infix "*" := TProd : ty_scope.
Infix "+" := TSum : ty_scope.
Notation "τ1 '→[' ℓ ] τ2" := (TArrow ℓ τ1 τ2) (at level 80, format "τ1  '→[' ℓ ]  τ2") : ty_scope.
Notation "∀ₜ: ℓ ; τ" := (TForall ℓ τ) (at level 100, τ at level 200) : ty_scope.
Notation "∀ₗ: ℓ ; τ" := (TLForall ℓ τ) (at level 100, τ at level 200) : ty_scope.
Notation "∃: τ" := (TExist τ) (at level 100, τ at level 200) : ty_scope.
Notation "'ref' τ" := (TRef τ) (at level 10, τ at next level, right associativity): ty_scope.

Notation "τ @ ℓ" := (TSec ℓ%label_term τ%type) (at level 60).
