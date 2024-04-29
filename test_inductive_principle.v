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


Inductive myterm (A B:Type) : nat -> list A -> list B-> Type :=
  | mynat : myterm A B 0 [] []
  | mynewterm (a:A) (n:nat) (l:list A) (l':list B) (v:myterm A B n l l') : myterm A B (S n) (a::l) l'
  .
MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm.