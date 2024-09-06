Require Import induction_principle.generate_inductive_principle List String.
Import ListNotations.
Import bytestring.


MetaCoq Run Derive InductivePrinciple nat as "indp_nat".
Print indp_nat.


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
  | mynewterm (a:A) (b:B) (n:nat) (l:list A) (l':list B) (v:myterm A B n l l') : myterm A B (S n) (a::l) (b::l')
  .
MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm.


Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l')
.
MetaCoq Run Derive InductivePrinciple All2 as "indp_all2".
Print indp_all2.


(* le defined with two indices *)
Inductive le: nat -> nat -> Type :=
| le_refl n : le n n
| le_S n m : le (S n) m -> le n m.
MetaCoq Run Derive InductivePrinciple le as "indp_le".
Print indp_le.

(* le defined with one non-uniform parameter and one index *)
Inductive le' (n: nat): nat -> Type :=
| le_refl' : le' n n
| le_S' m : le' (S n) m -> le' n m.
MetaCoq Run Derive InductivePrinciple le' as "indp_le'".
Print indp_le'.


Inductive rtree : Type := T : list rtree -> rtree.
MetaCoq Run Derive InductivePrinciple rtree as "indp_rtree". (* should raise an error message *)
Print indp_rtree.


Inductive ntree (A:Set) : Set :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  | nnil: nforest A
  | ncons : ntree A -> nforest A -> nforest A.
MetaCoq Run Derive InductivePrinciple ntree as "indp_ntree".
Print indp_ntree.


Inductive Point : Type :=
  | Pt : Config -> Config -> Point
with Line : Type :=
  | Ln : Point -> Point -> Line
  | Ext : Line -> Line
with Circle : Type :=
  | Crc : Line -> Point -> Figure -> Circle
with Figure : Type :=
  | P : Point -> Figure
  | L : Line -> Figure
  | C : Circle -> Figure
with Config : Type :=
  | Conf : list Figure -> Config
  .
MetaCoq Run Derive InductivePrinciple Point as "indp_point".
Print indp_point.


Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
	Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.
MetaCoq Run Derive InductivePrinciple Acc as "indp_acc".
Print indp_acc.



Inductive myt0 (A:Type) (B: Type) : Type :=
  | Build0 (x:A) (b:B) (c:
    (fun x => match x with
    | 0 => A
    | _ => A end) (3)
  ).
MetaCoq Run Derive InductivePrinciple myt0 as "indp_myt0".
Print indp_myt0.


Inductive myt (A:Type) (B: Type) : Type :=
  | Build (x:A) (b:B) (c:
    (let fix f x :=
      match x with
      | 0 => A
      | S n' => f n' end in f 3
    )
  ).
MetaCoq Run Derive InductivePrinciple myt as "indp_myt".
Print indp_myt.


Inductive myt1 (A:Type) (B: Type) : Type :=
  | Build1 (x:A) (b:B) (c:let x:= A in prod x B).
MetaCoq Run Derive InductivePrinciple myt1 as "indp_myt1".
Print indp_myt1.


Inductive testletin : let x := nat in x -> Type :=
  | C0: (let x := nat in x) -> (let y := option nat in prod y y ->
          nat) -> let z := nat in let w := z in w -> testletin 0.
MetaCoq Run Derive InductivePrinciple testletin as "indp_testletin".
Print indp_testletin.


Inductive mynat'' :Type :=
  | myz''
  | mys'' : let x := mynat'' in mynat'' -> mynat''.
MetaCoq Run Derive InductivePrinciple mynat'' as "indp_mynat''".
Print indp_mynat''.


Inductive myvec' (A:Type) : let x := nat in x -> Type :=
  | myvnil' : myvec' A 0
  | myvcons' : let a := A in a -> forall n, let z := myvec' in z a n -> myvec' A (S n).
MetaCoq Run Derive InductivePrinciple myvec' as "indp_myvec'".
Print indp_myvec'.


Inductive mynat' :Type :=
  | myz'
  | mys' : let x := mynat' in let y := x in ((fun z => z ) y) -> mynat'.
MetaCoq Run Derive InductivePrinciple mynat' as "indp_mynat'".
Print indp_mynat'.
