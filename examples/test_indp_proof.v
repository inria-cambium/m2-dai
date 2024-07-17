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
