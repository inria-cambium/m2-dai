Require Import generate_inductive_principle List String.
Import ListNotations.
Import bytestring.


Inductive myvec (A:Type) : nat -> Type :=
 | myvnil : myvec A 0
 | myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).

(* Definition thisfile := $run (tmCurrentModPath tt).
Definition input := ($run (tmQuoteInductive (thisfile, "myvec"))).
Compute (GenerateIndp_mutual (thisfile, "myvec") input). *)
MetaCoq Run Derive InductivePrinciple myvec as "indp_myvec".
Print indp_myvec.


Inductive myvec2 (A:Type) : nat -> Type :=
 | myvnil2 : myvec2 A 1
 | myvcons2 (x:A) (n:nat) (l:list A) (v1 v2:myvec2 A n) : myvec2 A (S n).
MetaCoq Run Derive InductivePrinciple myvec2 as "indp_myvec2".
Print indp_myvec2.


Inductive myterm (A B:Type) : nat -> list A -> list B-> Type :=
  | mynat : myterm A B 0 [] []
  | mynewterm (a:A) (b:B) (n:nat) (l:list A) (l':list B) (v:myterm A B n l l') : myterm A B (S n) (a::l) (b::l')
  .
MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm.


Inductive ntree (A:Set) : Set :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  | nnil: nforest A
  | ncons : ntree A -> nforest A -> nforest A.
MetaCoq Run Derive InductivePrinciple ntree as "indp_ntree".
Print indp_ntree.


Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l')
.
MetaCoq Run Derive InductivePrinciple All2 as "indp_all2".
Print indp_all2.


Fail MetaCoq Run Derive InductivePrinciple nat as "indp_nat".

Inductive rtree : Type := T : list rtree -> rtree.

Fail MetaCoq Run Derive InductivePrinciple rtree as "indp_rtree". (* should raise an error message *)

Require Import MetaCoqPrelude.

MetaCoq Run PrintInductivePrinciple Acc.

(* Check $Quote (forall [A : Type] [R : A -> A -> Prop] (P : A -> Type),
    (forall x : A, (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, Acc R x -> P x). *)

(* MetaCoq Run Derive InductivePrinciple Acc as "Acc_nat". *)
