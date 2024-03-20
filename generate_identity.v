Load MetaCoqPrelude.
Import MCMonadNotation.

Inductive bool :=
| true | false.

Compute $Quote bool.

Definition thisfile := $run (tmCurrentModPath tt).

Print thisfile.

MetaCoq Run (tmQuoteInductive (thisfile, "bool") >>= tmPrint).

(* input: *)
Definition input := {|
  ind_finite := Finite;
                ind_npars := 0;
                             ind_params := []%list;
                                           ind_bodies :=
          [{|
              ind_name := "bool";
              ind_indices := []%list;
              ind_sort := sType (Universe.make' Level.lzero);
              ind_type := tSort (sType (Universe.make' Level.lzero));
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
About input.

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

About tLambda.
Print aname.
Print binder_annot.
Print name.
Print relevance.

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

  About tInd.
  Print inductive.
  Print Instance.t.
  Search Instance.t.

End secondstep.

Inductive list X :=
| nil
| cons : X -> list X -> list X.

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

  About tCase.
  Print inductive.
  Print Instance.t.
  Search Instance.t.

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

Print constructor_body.
Print branch.

Compute GenerateIdentity (MPfile ["identity"]%list, "bool") input.

Inductive three :=
  zero | one | two.

MetaCoq Run (tmQuoteInductive (thisfile, "three")).

Definition input2 := ($run (tmQuoteInductive (thisfile, "three"))).

Print input2.

Compute $unquote (GenerateIdentity (thisfile, "three") input2).

Inductive nat :=
| O | S (n : nat).

Definition input3 := ($run (tmQuoteInductive (thisfile, "nat"))).
Print input3.

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

Compute $Quote id_nat.

Compute (GenerateIdentity (MPfile ["identity"]%list, "nat") input3).


Definition GenerateIdentity_recursive (na : kername) (i :  mutual_inductive_body) : term :=
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let the_name := {| binder_name := nNamed "x"; (* we just pick a name *)
                    binder_relevance := Relevant  |} (* not important for now, everything always Relevant *) in
  let the_constructors : list constructor_body := match i.(ind_bodies) with
                                                  | b :: _ => b.(ind_ctors)
                                                  | _ => nil
                                                  end in
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
                          (tRel 0) (mapi (fun i (b : constructor_body) =>
                                            {| bcontext := map (fun c : context_decl => c.(decl_name)) b.(cstr_args) ;
                                              bbody := tApp
                                                         (tConstruct the_inductive i Instance.empty)
                                                         (mapi (fun i (c : context_decl) => tApp (tRel todo) [(tRel todo)]) b.(cstr_args))
                                            |}
                                      ) the_constructors)) ;
           rarg := 0 |} ] 0
.

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
