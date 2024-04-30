Require Import generate_inductive_principle List.
Import ListNotations.

Inductive myvec (A:Type) : nat -> Type :=
 | myvnil : myvec A 0
 | myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
MetaCoq Run Derive InductivePrinciple myvec as "indp_myvec".
Print indp_myvec.


Inductive myvec2 (A:Type) : nat -> Type :=
 | myvnil2 : myvec2 A 1
 | myvcons2 (x:A) (n:nat) (l:list A) (v1 v2:myvec2 A n) : myvec2 A (S n).
MetaCoq Run Derive InductivePrinciple myvec2 as "indp_myvec2".
Print indp_myvec2.


Inductive myterm (A B:Type) : nat -> list A -> list B-> Type :=
  | mynat : myterm A B 0 [] []
  | mynewterm (a:A) (n:nat) (l:list A) (l':list B) (v:myterm A B n l l') : myterm A B (S n) (a::l) l'
  .
MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm.

Fail MetaCoq Run Derive InductivePrinciple nat as "indp_nat".

Inductive rtree : Type := T : list rtree -> rtree.

Fail MetaCoq Run Derive InductivePrinciple rtree as "indp_rtree". (* should raise an error message *)

Require Import MetaCoqPrelude.

MetaCoq Run PrintInductivePrinciple Acc.

Check $Quote (forall [A : Type] [R : A -> A -> Prop] (P : A -> Type),
    (forall x : A, (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, Acc R x -> P x).

(* MetaCoq Run Derive InductivePrinciple Acc as "Acc_nat". *)


(* Inductive Mybool := myt | myf.
Print Mybool_ind.

Inductive ntree (A:Set) : Set :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  | nnil: nforest A
  | ncons : ntree A -> nforest A -> nforest A.
Print ntree_ind. *)
