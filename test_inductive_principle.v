Load generate_inductive_principle.


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

Inductive myterm (A B:Type) : nat -> list A -> Type :=
  | mynat : myterm A B 0 [].

Print myterm_ind.
Check $quote (forall (A B : Type)
(P : forall (n : nat) (l : list A), myterm A B n l -> Prop),
P 0 [] (mynat A B) ->
forall (n : nat) (l : list A) (m : myterm A B n l), P n l m).


Definition thisfile := $run (tmCurrentModPath tt).
Definition input_myterm := ($run (tmQuoteInductive (thisfile, "myterm"))).
Compute (GenerateIndp (thisfile, "myterm") input_myterm).


MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm.