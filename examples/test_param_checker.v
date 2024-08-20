Require Import MetaCoq.Programming.

Definition thisfile := $run (tmCurrentModPath tt).

Inductive myvec (A:Type) : nat -> Type :=
| myvnil : myvec A 0
| myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
Definition input := ($run (tmQuoteInductive (thisfile, "myvec"))).
Compute (CheckUniformParam (thisfile, "myvec") input).

Inductive le: nat -> nat -> Type :=
| le_refl n : le n n
| le_S n m : le (S n) m -> le n m.
Definition input_le := ($run (tmQuoteInductive (thisfile, "le"))).
Compute (CheckUniformParam (thisfile, "le") input_le).

Inductive le'  (A:Type)(n : nat) (B:Type): nat -> Type :=
| le_refl' : le'   A n B n
| le_S' m : le' A (S n)  (A*B) m -> le'  (A) n B n ->le' A n  B m.
Definition input_le':= ($run (tmQuoteInductive (thisfile, "le'"))).
Compute (CheckUniformParam (thisfile, "le'") input_le').

Inductive le0' (n : nat): nat -> Type :=
| le0_refl' : le0'  n  n
| le0_S' m : le0' n  m -> le0' n n ->le0' n  m
with smt (n:nat) : Type := STH (m:nat) (_:smt m) : smt n
.
Definition input_le0':= ($run (tmQuoteInductive (thisfile, "le0'"))).
Compute (CheckUniformParam (thisfile, "le0'") input_le0').
(* Check le0'_ind. *)


Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
	Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.
Definition input_acc:= ($run (tmQuoteInductive (thisfile, "Acc"))).
Compute (CheckUniformParam (thisfile, "Acc") input_acc).

Inductive Acc' (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
	Acc_intro' : (let a := A in forall y : a, R y x -> Acc' A R y) -> Acc' A R x.
Definition input_acc':= ($run (tmQuoteInductive (thisfile, "Acc'"))).
Compute (CheckUniformParam (thisfile, "Acc'") input_acc').


Inductive nunest (A B C : Type) : Type :=
| nunest_nil : A -> nunest A B C
| nunest_cons : list (nunest A (B * B) C) -> nunest A B C.
Definition input_nunest := ($run (tmQuoteInductive (thisfile, "nunest"))).
Compute (CheckUniformParam (thisfile, "nunest") input_nunest).

