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

  (*for inductive type A *)
  (*check the type of an arg is of form: _ -> _-> _-> A*)
  let fix check_type (t:term) (n:Nat.t): bool :=
    match t with
    | tProd _ _ t => check_type t (n+1)
    | tRel i => if eqb i n then true else false
    | _ => false
    end in
  
  let fix lift (t:term) :term :=
    match t with
    | tRel i => tRel (i+1)
    | tApp t1 tl => tApp (lift t1) (map lift tl)
    | _ => todo
    end in

  let fix transformer (t:term) (u:term) (n:Nat.t):=
    match t with
    | tProd _ t1 t2 => tLambda the_name t1 (transformer t2 (tApp (lift u) [tRel 0]) n)
    | tRel i => tApp (tRel (i+n)) [u] (*plus 2*) 
    | _ => todo 
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
                  let fix Ffix t :=
                    match t with
                    | tRel j => 
                        if eqb (j) (b.(cstr_arity)-1-i) then    
                          tApp (tRel (b.(cstr_arity) + 1)) [(tRel (i))]
                        else tRel (i)
                    | tProd _ t1 t2 =>
                        let index := b.(cstr_arity)-1-i+1 in
                        if (check_type t2 index) then transformer t (tRel i) (2+i)
                        else tRel i
                    (* todo *)
                    | _ => tRel (i) end 
                  in Ffix arg.(decl_type))
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


Inductive nat':=
| zero' | S' (n m : nat') | newS (k:nat) | S'' (n:Type) (m:n).
Definition input4 := ($run (tmQuoteInductive (thisfile, "nat'"))).
(* Print input4. *)
Compute $unquote (GenerateIdentity_recursive (thisfile, "nat'") input4).



Inductive term2 : Type :=
| Var2 (n:nat)
| App (t1 t2:term2)
| Lam (f: nat -> nat-> term2)
| Lam2 (f1: nat -> term2) (f2:nat -> term2)
.
Definition input_term2 := ($run (tmQuoteInductive (thisfile, "term2"))).
Compute $unquote (GenerateIdentity_recursive (thisfile, "term2") input_term2).

(* 
(*todo*)






(* TODO list:
   - simple, non-recursive types (bool) DONE
   - simple, recursive types (nat) DONE
   - recursive types with parameters (list) DONE
   - mutual inductive types
   - recursive types with indices and parameters (Vector.t)
 *)

(* long term TODO list:
  - new term representation with names for MetaCoq
  - re-implement GenerateIdentity with named term representation
  - compare what is easier
 *)



Fixpoint listmake (X:Type) (x:X) (n:Datatypes.nat) :=
  match n with
  | Datatypes.O => []
  | Datatypes.S n => cons x (listmake _ x n) end.



Definition GenerateIdentity_param (na : kername) (ty :  mutual_inductive_body) : term :=

  let n_inductives := length ty.(ind_bodies) in
  let the_name := {| binder_name := nNamed "x";
                    binder_relevance := Relevant  |}
  in

  let plus' (k:Datatypes.nat) (tl: list term) :  list term :=
    map (fun x => match x with tRel i => tRel (i+k) | _ => todo end) tl
  in

  let params := ty.(ind_params) in

  let myf (i:Datatypes.nat) (body: one_inductive_body) :=

    let the_inductive := {| inductive_mind := na; inductive_ind := i |} in

    let indices :=  body.(ind_indices) in
    let seq_indice := 
      map (fun i => tRel i) (rev (seq 0 (length indices))) 
    in
    let seq_param :=
      plus' (length indices)
        (map (fun i => tRel i) (rev (seq 0 (length params))))
    in
    let seq_indice_param := seq_param ++ seq_indice in
    let aux : Nat.t -> constructor_body -> branch term := fun i b =>
      {| bcontext := map (fun _ => the_name (*name not important*)) b.(cstr_args) ;
        bbody :=
          let narg := length b.(cstr_args) in
          let index_param := b.(cstr_arity) + ty.(ind_npars) in
          if eqb (ty.(ind_npars)+length indices) 0 then
            (*for non parametric type*)
            tApp
              (tConstruct the_inductive i Instance.empty)
              (rev
                (mapi
                  (fun i arg => 
                    let Ffix t :=
                      match t with
                      | tRel j => 
                        if andb (leb (b.(cstr_arity)-1-i) j)
                            (leb j (b.(cstr_arity)-1-i + n_inductives -1))
                        then    
                          tApp (tRel (j + 1 + i + 1)) [tRel i]
                        else tRel (i)
                      (* todo *)
                      | _ => tRel (i) end 
                    in Ffix arg.(decl_type))
                    b.(cstr_args)))
          else
            (*for type with parameter/indice*)
            tApp
              (tConstruct the_inductive i Instance.empty)
                ((plus' (1 + b.(cstr_arity)) seq_param)
                  ++
                (rev
                  (mapi
                    (fun i arg =>
                      match arg.(decl_type) with
                      (*for type with indice/parameter*)
                      | tApp (tRel j) tl =>
                        if andb (leb (index_param-1-i) j) 
                              (leb j (index_param-1-i + n_inductives -1 )) 
                        then
                          tApp (tRel (2 + j + i + length indices))
                            ((map 
                              (fix Ffix (t:term) : term :=
                                match t with
                                | tRel k =>
                                  if leb (narg-i-1) k then 
                                    tRel (k+1+i+1+length indices) 
                                  else tRel (k+i+1)
                                | tApp tx tl => tApp (Ffix tx) (map Ffix tl)
                                (*todo*)
                                | _ => t
                                end) tl)
                              ++ [tRel i])
                        else tRel i
                        (*todo*)
                      | _ => tRel i end)
                    b.(cstr_args))))
      |}
    in

    {|
      dname := {| binder_name := nNamed "id" ; 
                  binder_relevance := Relevant |};
      dtype :=  
        it_mkProd_or_LetIn (indices ++ params)
          (tProd the_name
            (tApp
              (tInd the_inductive Instance.empty)
              seq_indice_param)
            (tApp
              (tInd the_inductive Instance.empty)
              (plus' 1 seq_indice_param))
          );

      dbody :=
        it_mkLambda_or_LetIn (indices ++ params)
        (tLambda the_name (tApp (tInd the_inductive Instance.empty) seq_indice_param)
          (tCase
            {|
              ci_ind := the_inductive ;
              ci_npar := length params;
              ci_relevance := Relevant
            |}
            {|
              puinst := []%list;
              pparams := plus' 1 seq_param; 
              pcontext := listmake _ the_name (1 + (length indices)); 
              preturn :=
                tApp (tInd the_inductive Instance.empty) 
                  ((plus' (1 + 1 + length indices) seq_param) ++ (plus' 1 seq_indice))
            |}
            (tRel 0)
            (mapi aux body.(ind_ctors))
          ));
      rarg := length indices + length params
    |}
  in
  tFix (mapi myf ty.(ind_bodies)) 0
.


(*the result of previous examples still correct*)
Compute $unquote (GenerateIdentity_param (thisfile, "three") input2).
Compute $unquote (GenerateIdentity_param (thisfile, "nat") input3).



Inductive list' (X:Type) :=
| nil'
| cons' : X -> list' X -> list' X.
Definition input5 := ($run (tmQuoteInductive (thisfile, "list'"))).
Compute $unquote (GenerateIdentity_param (thisfile, "list'") input5).


Inductive Fin0 (n:nat) : Set :=
| fzero0: Fin0 n
| fS0: Fin0 n -> Fin0 n.
Definition inputf0 := ($run (tmQuoteInductive (thisfile, "Fin0"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Fin0") inputf0).


Inductive list2 (X:Type) :=
| mynil
| mynil3
| mycons : X -> X -> list2 X -> list2 X -> list2 X
| mycons2 : X -> list2 X -> X -> list2 X -> list2 X
| strange : list2 nat -> list2 X
| strange2 : list X -> list2 X.
Definition input6 := ($run (tmQuoteInductive (thisfile, "list2"))).
Compute $unquote (GenerateIdentity_param (thisfile, "list2") input6).


Inductive list3 (A:Set) : Set :=
| nil3 : list3 A
| cons3 : A -> list3 (A*A*A) -> list3 A.
Definition input7 := ($run (tmQuoteInductive (thisfile, "list3"))).
Compute $unquote (GenerateIdentity_param (thisfile, "list3") input7).


Inductive mterm (n:nat): Type :=
| mVar
| mApp (a b:nat) (x: mterm a) (y:mterm b).
Definition input' := ($run (tmQuoteInductive (thisfile, "mterm"))).
Compute $unquote (GenerateIdentity_param (thisfile, "mterm") input').


(*multiple parameters*)
Inductive All2' (A B : Type) (R : A -> B -> Type) : Type :=
| All2'_nil : All2' A B R
| All2'_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
              R x y -> All2' A B R -> All2' A B R
. 
Definition inputa' := ($run (tmQuoteInductive (thisfile, "All2'"))).
Compute $unquote (GenerateIdentity_param (thisfile, "All2'") inputa').


(* Indice *)
Inductive Fin: nat -> Set :=
| fzero n : Fin n
| fS n: Fin n -> Fin (S n)
.
Definition inputf := ($run (tmQuoteInductive (thisfile, "Fin"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Fin") inputf).


Inductive test0 : nat -> nat -> Set :=
| t0 : test0 O O
| tSS : forall n, test0 n (S n) -> test0 (S (S n)) n.
Definition input_t := ($run (tmQuoteInductive (thisfile, "test0"))).
Compute $unquote (GenerateIdentity_param (thisfile, "test0") input_t).


(*with both parameter and indice*)
Inductive vec (X:Type) : nat -> Type:=
  | vnil : vec X O
  | vcons : X -> forall n:nat, vec X n -> vec X (S n).
Definition input_vec := ($run (tmQuoteInductive (thisfile, "vec"))).
Compute $unquote (GenerateIdentity_param (thisfile, "vec") input_vec).
(* Definition f0 := $unquote (GenerateIdentity_param (thisfile, "vec") input_vec).
Goal forall X, forall n, forall v:vec X n, f0 X n v = v.
Proof.
  induction v.
  - auto.
  - simpl. rewrite IHv. auto.
Qed. *)


Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l').
Definition input_all2 := ($run (tmQuoteInductive (thisfile, "All2"))).
Compute $unquote (GenerateIdentity_param (thisfile, "All2") input_all2).


(*mutual inductive type*)
Inductive ntree (A:Set) : Set :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  | nnil: nforest A
  | ncons (a:ntree A) (b:nforest A): nforest A
.
(* Parameters should be syntactically the same for each inductive type. *)
Definition inputtree := ($run (tmQuoteInductive (thisfile, "ntree"))).
Compute $unquote (GenerateIdentity_param (thisfile, "ntree") inputtree).


Inductive ntree2 (A:Set) : nat -> Set :=
  nnode2 (a:A) (n:nat) : nforest2 A -> ntree2 A n
with nforest2 (A:Set) : Set :=
  | nnil2: nforest2 A
  | ncons2 (n:nat) (a:ntree2 A n) (b:nforest2 A): nforest2 A
.
Definition inputtree2 := ($run (tmQuoteInductive (thisfile, "ntree2"))).
Compute $unquote (GenerateIdentity_param (thisfile, "ntree2") inputtree2).


Inductive Point : Type :=
  | Pt : Config -> Config -> Point
with Line : Type :=
  | Ln : Point -> Point -> Line
  | Ext : Line -> Line
with Circle : Type :=
  | Crc : Point -> Line -> Circle
with Figure : Type :=
  | P : Point -> Figure
  | L : Line -> Figure
  | C : Circle -> Figure
with Config : Type :=
  | Conf : list Figure -> Config.
Definition inputpoint := ($run (tmQuoteInductive (thisfile, "Point"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Point") inputpoint).
  