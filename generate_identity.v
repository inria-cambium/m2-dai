Load MetaCoqPrelude.
Import MCMonadNotation.

Inductive bool :=
| true | false.

Compute $Quote bool.

Definition thisfile := $run (tmCurrentModPath tt).

Print thisfile.

Definition s := $run (tmQuoteInductive (thisfile, "bool")).

(* Print s. *)

(* input: *)
(* Definition input := {|
  ind_finite := Finite;
                ind_npars := 0;
                             ind_params := []%list;
                                           ind_bodies :=
          [{|
              ind_name := "bool";
              ind_indices := []%list;
              ind_sort := Universe.of_levels (inr Level.lzero);
              ind_type := tSort (Universe.of_levels (inr Level.lzero));
              ind_kelim := IntoAny;
              ind_ctors :=
                [{| cstr_name := "true"; cstr_args := []%list; cstr_indices := []; cstr_type := tRel 0; cstr_arity := 0 |};
                 {| cstr_name := "false"; cstr_args := []%list; cstr_indices := []; cstr_type := tRel 0; cstr_arity := 0 |}];
              ind_projs := [];
              ind_relevance := Relevant
            |}];
          ind_universes := Monomorphic_ctx;
                           ind_variance := None
|}.
About input. *)

(* output: *)
(* = tLambda {| binder_name := nNamed "b"; binder_relevance := Relevant |} *)
(*     (tInd {| inductive_mind := (MPfile ["identity"]%list, "bool"); inductive_ind := 0 |} []%list) *)
(*     (tCase *)
(*        {| *)
(*          ci_ind := {| inductive_mind := (MPfile ["identity"]%list, "bool"); inductive_ind := 0 |}; *)
(*          ci_npar := 0; *)
(*          ci_relevance := Relevant *)
(*        |} *)
(*        {| *)
(*          puinst := []%list; *)
(*          pparams := []; *)
(*          pcontext := [{| binder_name := nNamed "b"; binder_relevance := Relevant |}]; *)
(*          preturn := *)
(*            tInd {| inductive_mind := (MPfile ["identity"]%list, "bool"); inductive_ind := 0 |} []%list *)
(*        |} (tRel 0) *)
(*        [{| *)
(*           bcontext := []; *)
(*           bbody := *)
(*             tConstruct {| inductive_mind := (MPfile ["identity"]%list, "bool"); inductive_ind := 0 |} 0 *)
(*               []%list *)
(*         |}; *)
(*         {| *)
(*           bcontext := []; *)
(*           bbody := *)
(*             tConstruct {| inductive_mind := (MPfile ["identity"]%list, "bool"); inductive_ind := 0 |} 1 *)
(*               []%list *)
(*         |}]) *)

(* MetaCoq Run GenerateIdentity bool. *)

Definition id_bool (b : bool) :=
  match b as b return bool with
  | true => true
  | false => false
  end.

Axiom todo : forall {A}, A.

Module firststep.

Definition GenerateIdentity (i :  mutual_inductive_body) : term :=
  tLambda {| binder_name := nNamed "x"; (* we just pick a name *)
             binder_relevance := Relevant  |} (* not important for now, everything always Relevant *)
    todo todo.

(* About tLambda.
Print aname.
Print binder_annot.
Print name.
Print ident.
Print relevance. *)

End firststep.

Inductive test :=
| T (a : test2)
with test2 :=
| T2 (b : test).

Compute ($Quote test, $Quote test2).

Module secondstep.

  Definition GenerateIdentity (na : kername) (i :  mutual_inductive_body) : term :=
    tLambda {| binder_name := nNamed "x"; (* we just pick a name *)
              binder_relevance := Relevant  |} (* not important for now, everything always Relevant *)
      (tInd {| inductive_mind := na; inductive_ind := 0 |} Instance.empty)
      todo.

 (*  About tInd.
  Print inductive.
  Print Instance.t. *)
  (* Search Instance.t. *)

End secondstep.

Module thirdstep.

  Definition GenerateIdentity (na : kername) (i :  mutual_inductive_body) : term :=
    let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
    let the_name := {| binder_name := nNamed "x"; (* we just pick a name *)
                      binder_relevance := Relevant  |} (* not important for now, everything always Relevant *) in
    tLambda the_name
      (tInd the_inductive Instance.empty)
      (tCase
         {| (* information about the type we do case analysis on *)
           ci_ind := the_inductive ;
           ci_npar := 0;        (* this is going to change once we cover mutual inductive types *)
           ci_relevance := Relevant
         |}
         {|
           puinst := []%list;   (* this is going to change once we cover universe levels *)
           pparams := [];       (* this is going to change once we cover types with parameters *)
           pcontext := [the_name];
           preturn := tInd the_inductive Instance.empty
       |}
         todo todo).

 (*  About tCase.
  Print inductive.
  Print Instance.t. *)
  (* Search Instance.t. *)

End thirdstep.

Require Import List.
Import ListNotations.


Definition GenerateIdentity (na : kername) (i :  mutual_inductive_body) : term :=
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let the_name := {| binder_name := nNamed "x"; (* we just pick a name *)
                    binder_relevance := Relevant  |} (* not important for now, everything always Relevant *) in
  let the_constructors : list constructor_body := match i.(ind_bodies) with
                                                  | b :: _ => b.(ind_ctors)
                                                  | _ => nil
                                                  end in
  tLambda the_name
    (tInd the_inductive Instance.empty)
    (tCase
       {| (* information about the type we do case analysis on *)
         ci_ind := the_inductive ;
         ci_npar := 0;        (* this is going to change once we cover mutual inductive types *)
         ci_relevance := Relevant
       |}
       {|
         puinst := []%list;   (* this is going to change once we cover universe levels *)
         pparams := [];       (* this is going to change once we cover types with parameters *)
         pcontext := [the_name];
         preturn := tInd the_inductive Instance.empty
       |}
       (tRel 0) (mapi (fun i b =>
                         {| bcontext := [];
                           bbody := tConstruct the_inductive i Instance.empty |}
                   ) the_constructors)).

(* Print constructor_body.
Print mutual_inductive_body.
Print one_inductive_body.
Print branch. *)

(* Compute GenerateIdentity (MPfile ["identity"]%list, "bool") input. *)

Inductive three :=
  zero | one | two.

MetaCoq Run (tmQuoteInductive (thisfile, "three")).

Definition input2 := ($run (tmQuoteInductive (thisfile, "three"))).

(* Print input2. *)

Compute $unquote (GenerateIdentity (thisfile, "three") input2).

Inductive nat :=
| O | S : nat -> nat.

Definition input3 := ($run (tmQuoteInductive (thisfile, "nat"))).
(* Print input3. *)

(* cstr_args := *)
(*   [{| *)
(*       decl_name := {| binder_name := nNamed "n"; binder_relevance := Relevant |}; *)
(*       decl_body := None; *)
(*       decl_type := tRel 0 *)
(*     |}]; *)

Fixpoint id_nat (n : nat) :=
  match n with
  | O => O
  | S m => S (id_nat m)
  end.

(* bcontext := [{| binder_name := nNamed "m"; binder_relevance := Relevant |}]; *)

(* Compute $Quote id_nat. *)

(* Compute (GenerateIdentity (MPfile ["identity"]%list, "nat") input3). *)

(* Search list. *)

(* Search rev. *)

(* Search (Datatypes.nat -> Datatypes.nat -> Datatypes.bool). *)

Definition GenerateIdentity_recursive (na : kername) (i :  mutual_inductive_body) : term :=
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let the_name := {| binder_name := nNamed "y"; (* we just pick a name *)
                    binder_relevance := Relevant  |} (* not important for now, everything always Relevant *) in
  let the_constructors : list constructor_body := match i.(ind_bodies) with
                                                  | b :: _ => b.(ind_ctors)
                                                  | _ => nil
                                                  end in

  let aux : Nat.t -> constructor_body -> branch term := fun i b =>
    {| bcontext := map (fun c : context_decl => the_name) b.(cstr_args) ;
       bbody :=
        match b.(cstr_args) with
        | [] => tConstruct the_inductive i Instance.empty
        | args =>
           tApp
            (tConstruct the_inductive i Instance.empty)
            (rev
              (mapi
                (fun i arg => 
                  match arg.(decl_type) with
                  | tRel j => 
                      (* check *)
                      if eqb j (b.(cstr_arity)-1-i) then    
                         tApp (tRel (b.(cstr_arity) + 1)) [(tRel i)]
                      else tRel i
                  | _ => tRel i end )
                args))
        end
    |}
  in

  tFix [ {| dname := {| binder_name := nNamed "id" ; binder_relevance := Relevant |} ;
           dtype := tProd {| binder_name := nAnon ; binder_relevance := Relevant |}
                      (tInd the_inductive Instance.empty) (tInd the_inductive Instance.empty);
           dbody :=  tLambda the_name
                       (tInd the_inductive Instance.empty)
                       (tCase
                          {|
                            ci_ind := the_inductive ;
                            ci_npar := 0;
                            ci_relevance := Relevant
                          |}
                          {|
                            puinst := []%list;
                            pparams := [];
                            pcontext := [the_name];
                            preturn := tInd the_inductive Instance.empty
                          |}
                          (tRel 0) (mapi aux the_constructors)) ;
           rarg := 0 |} ] 0
.



(* Compute $Quote id_nat. *)

Compute $unquote (GenerateIdentity_recursive (thisfile, "three") input2).

Compute $unquote (GenerateIdentity_recursive (thisfile, "nat") input3).


(* About tLambda.
About tCase.
Print tCase.
Print branch.
Compute $Quote id_nat.
Print constructor_body.
Print input3. *)

Inductive nat':=
| zero' | S' (n m : nat') | newS (k:nat) | S'' (n:Type) (m:n).
Definition input4 := ($run (tmQuoteInductive (thisfile, "nat'"))).
(* Print input4. *)
Compute $unquote (GenerateIdentity_recursive (thisfile, "nat'") input4).

(* TODO list:
   - simple, non-recursive types (bool) DONE
   - simple, recursive types (nat) ALMOST DONE
   - recursive types with parameters (list)
   - mutual inductive types
   - recursive types with indices and parameters (Vector.t)
 *)

(* long term TODO list:
  - new term representation with names for MetaCoq
  - re-implement GenerateIdentity with named term representation
  - compare what is easier
 *)


(* Inductive mylist (X:Type) : Type :=
  | mynil : mylist X
  | mycons (x : X) (l: mylist X) : mylist X. *)
(* Arguments mynil {X}.
Arguments mycons {X}. *)

Inductive list' (X:Type) :=
| nil'
| cons' : X -> list' X -> list' X.
(* Arguments nil' {X}.
Arguments cons' {X}. *)


Definition input5 := ($run (tmQuoteInductive (thisfile, "list'"))).
(* Print input5. *)
(* About List.
About cons.
About list.
Print list. *)
(* Print Datatypes.list. *)
(* Print Level.level. *)

 (* Fixpoint id_list (X:Type) (l:list' X): list' X :=
  match l with
  | nil' => nil' X
  | cons' x l1 => cons' X x (id_list _ l1)
  end.
 Compute $Quote id_list.  *)


Definition GenerateIdentity_param (na : kername) (ty :  mutual_inductive_body) : term :=

  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let the_name := {| binder_name := nNamed "x";
                    binder_relevance := Relevant  |}
  in
  (* single param *)
(*   let type_param:=
    match ty.(ind_params) with
    | x :: _ =>
      match x.(decl_type) with
      | tSort s => tSort s (** todo **)
      | _ => todo
      end
    | nil => todo
    end
  in *)
  

  let aux : Nat.t -> constructor_body -> branch term := fun i b =>
    {| bcontext := map (fun _ => the_name (*name not important*)) b.(cstr_args) ;
       bbody :=
        match b.(cstr_args) with
        | [] => tApp (tConstruct the_inductive i []) [tRel 1]
        | args =>
           let index_param := b.(cstr_arity) + ty.(ind_npars) in
           tApp
            (tConstruct the_inductive i Instance.empty)
              ([tRel index_param] (** must have this type parameter ? **)
              ++
              (rev
                (mapi
                  (fun i arg =>

                    match arg.(decl_type) with
                    | tApp (tRel j) tl =>
                        (* check the type *)
                        if eqb j (index_param-1-i) then
                          tApp (tRel (index_param+1))
                            ((map (fix Ffix (t:term) : term :=
                                      match t with
                                      | tRel _ => tRel index_param
                                      (* | tRel k => tRel (k+1+i+1) *)
                                      | tApp tx tl => tApp (Ffix tx) (map Ffix tl)
                                      | _ => t
                                      end) tl) 
                              ++ [tRel i])
                        else tRel i
                    | _ => tRel i
                    end)
                  args)))
        end
    |}
  in

  let the_constructors : list constructor_body := match ty.(ind_bodies) with
                                          | b :: _ => b.(ind_ctors)
                                          | _ => nil
                                          end in

  tFix [ {| dname := {| binder_name := nNamed "id" ; binder_relevance := Relevant |} ;
            dtype :=
              it_mkProd_or_LetIn ty.(ind_params)
                (tProd the_name
                  (tApp
                    (tInd the_inductive Instance.empty)
                    [tRel 0])
                  (tApp
                    (tInd the_inductive Instance.empty)
                    [tRel 1])
                );

            dbody :=
              it_mkLambda_or_LetIn ty.(ind_params)
                (tLambda the_name (tApp (tInd the_inductive Instance.empty) [tRel 0])
                  (tCase
                    {|
                      ci_ind := the_inductive ;
                      ci_npar := 1;
                      ci_relevance := Relevant
                    |}
                    {|
                      puinst := []%list;
                      pparams := [tRel 1];
                      pcontext := [the_name];
                      preturn :=
                        tApp (tInd the_inductive Instance.empty) [tRel 2]
                    |}
                    (tRel 0)
                    (mapi aux the_constructors)
                  )) ;
            rarg := length (ty.(ind_params)) (** todo **) |} ] 0
.

Compute $unquote (GenerateIdentity_param (thisfile, "list'") input5).


Inductive list2 (X:Type) :=
| mynil
| mynil3
| mycons : X -> X -> list2 X -> list2 X -> list2 X
| mycons2 : X -> list2 X -> X -> list2 X -> list2 X
| strange : list2 nat -> list2 X
| strange2 : list X -> list2 X.


Inductive list3 (A:Set) : Set :=
| nil3 : list3 A
| cons3 : A -> list3 (A*A*A) -> list3 A.



Inductive Fin (n:nat) : Set :=
| fzero: Fin n
| fS: Fin n -> Fin n.
Definition inputf := ($run (tmQuoteInductive (thisfile, "Fin"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Fin") inputf).




(* 
Inductive even : nat -> Set :=
| even0 : even O
| evenSS : forall n, even n -> even (S (S n)).


Fixpoint id_even (n: nat) (p : even n) : even n :=
  match p with
  | even0 => even0
  | evenSS _ q => evenSS _ (id_even _ q) end .

Compute $Quote id_even.


Definition input6 := ($run (tmQuoteInductive (thisfile, "even"))).
Print input6.

Print input7.

Print input5. *)


Definition input6 := ($run (tmQuoteInductive (thisfile, "list2"))).
(* Print input6. *)
Compute $unquote (GenerateIdentity_param (thisfile, "list2") input6).
Definition input7 := ($run (tmQuoteInductive (thisfile, "list3"))).
Compute $unquote (GenerateIdentity_param (thisfile, "list3") input7).










