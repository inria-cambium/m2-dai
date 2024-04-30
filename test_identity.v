Require Import generate_identity List.
Import ListNotations.

(* Definition thisfile := $run (tmCurrentModPath tt).
Inductive Fin: nat -> nat -> nat -> Set :=
| fzero n : Fin n n n
| fS n: Fin n n n -> Fin n n n
.
Definition inputf := ($run (tmQuoteInductive (thisfile, "Fin"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Fin") inputf). *)

Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l')
.
MetaCoq Run Derive Identity All2 as "id_all2".
Print id_all2.


Inductive vec' (X:Type) : nat -> Type:=
  | vnil' : vec' X O
  | vcons' : X -> forall n:nat, vec' X n -> vec' X (S n)
  .
MetaCoq Run Derive Identity vec' as "id_vec'".
Print id_vec'.


(*type constructor with lambda argument*)
Inductive Acc (A : Type) (R : A -> A -> Type) (x : A) : Type :=
	Acc_intro  :
  (forall y : A, R y x -> Acc A R y) ->
  Acc A R x.
MetaCoq Run Derive Identity Acc as "id_acc".
Print id_acc.


Inductive ntree2 (A:Set) : nat -> Set :=
  nnode2 (a:A) (n:nat) : nforest2 A -> ntree2 A n
with nforest2 (A:Set) : Set :=
  | nnil2: nforest2 A
  | ncons2 (n:nat) (a:ntree2 A n) (b:nforest2 A): nforest2 A
.
MetaCoq Run Derive Identity ntree2 as "id_ntree2".
Print id_ntree2.


Inductive Point : Type :=
  | Pt : Config -> Config -> Point
with Line : Type :=
  | Ln : Point -> Point -> Line
  | Ext : Line -> Line
with Circle : Type :=
  | Crc : (nat -> Line) -> Point -> Figure-> Circle
with Figure : Type :=
  | P : Point -> Figure
  | L : Line -> Figure
  | C : (nat -> Circle) -> Figure
with Config : Type :=
  | Conf : list Figure -> Config
with R : nat -> Type := R0 : R O | Rs: forall n, Point -> R n -> R (S n)
with R' :Set := R's : forall n, R n -> R'
.
MetaCoq Run Derive Identity Point as "id_point".
Print id_point.


Inductive ntree3 (A:Set) : nat -> Set :=
  nnode3 (a:A) (n:nat) : (nat -> nforest3 A) -> nat -> ntree3 A n
with nforest3 (A:Set) : Set :=
  | nnil3: nforest3 A
  | ncons3 (n:nat) (_:nat -> ntree3 A n) (_:nforest3 A): nforest3 A
.
MetaCoq Run Derive Identity ntree3 as "id_ntree3".
Print id_ntree3.
