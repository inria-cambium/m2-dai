Require Import generate_indp_proof List String.
Import ListNotations.
Import bytestring.

Inductive myvec (A:Type) : nat -> Type :=
| myvnil : myvec A 0
| myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
MetaCoq Run Derive InductivePrinciple myvec as "indp_myvec".
Print indp_myvec.


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


Inductive le: nat -> nat -> Type :=
| le_refl n : le n n
| le_S n m : le (S n) m -> le n m.
MetaCoq Run Derive InductivePrinciple le as "indp_le".
Print indp_le.

Inductive le' (n: nat): nat -> Type :=
| le_refl' : le' n n
| le_S' m : le' (S n) m -> le' n m.
MetaCoq Run Derive InductivePrinciple le' as "indp_le'".
Print indp_le'.


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


(* Inductive testletin : let x := nat in x -> Type :=
  | C0: (let x := nat in x) -> (let y := option nat in prod y y ->
          nat) -> let z := nat in let w := z in w -> testletin 0. *)
(* MetaCoq Run PrintInductivePrinciple testletin. *)
(* Unset Guard Checking. *)
(* MetaCoq Run Derive InductivePrinciple testletin as "indp_testletin". *)
(* Print testletin_ind. *)
(* Load MetaCoqPrelude. *)
(* Compute $Quote fun (P : let x := nat in forall x0 : x, testletin x0 -> Prop)
(f : forall (p : let x := nat in x)
     (n : let y := option nat in y * y -> nat),
     let z := nat in let w := z in forall w0 : w, P 0 (C0 p n w0)) =>
let x := nat in
fun (f0 : x) (t : testletin f0) =>
match t as t0 in (@testletin x0 f1) return (P f1 t0) with
| C0 p n z w w0 => f p n w0
end. *)


Inductive mynat'' :Type :=
  | myz''
  | mys'' : let x := mynat'' in mynat'' -> mynat''.
MetaCoq Run Derive InductivePrinciple mynat'' as "indp_mynat''".
Print indp_mynat''.


(* Inductive myvec' (A:Type) : let x := nat in x -> Type :=
  | myvnil' : myvec' A 0
  | myvcons' : let a := A in a -> forall n, let z := myvec' in z a n -> myvec' A (S n).
MetaCoq Run Derive InductivePrinciple myvec' as "indp_myvec'".
Print indp_myvec'. *)


Inductive mynat' :Type :=
  | myz'
  | mys' : let x := mynat' in let y := x in ((fun z => z ) y) -> mynat'.
MetaCoq Run Derive InductivePrinciple mynat' as "indp_mynat'".
Print indp_mynat'.
