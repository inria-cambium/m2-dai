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

(* Inductive nat0 :=
| O | S : nat0 -> nat0. *)

(* Definition input3 := ($run (tmQuoteInductive (thisfile, "nat0"))). *)
(* Print input3. *)

(* cstr_args := *)
(*   [{| *)
(*       decl_name := {| binder_name := nNamed "n"; binder_relevance := Relevant |}; *)
(*       decl_body := None; *)
(*       decl_type := tRel 0 *)
(*     |}]; *)

(* Fixpoint id_nat0 (n : nat0) :=
  match n with
  | O => O
  | S m => S (id_nat0 m)
  end. *)


Definition GenerateIdentity_recursive (na : kername) (i :  mutual_inductive_body) : term :=
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let the_name := {| binder_name := nNamed "y"; (* we just pick a name *)
                    binder_relevance := Relevant  |} (* not important for now, everything always Relevant *) in
  let the_constructors : list constructor_body := match i.(ind_bodies) with
                                                  | b :: _ => b.(ind_ctors)
                                                  | _ => nil
                                                  end in

  let aux : Nat.t -> constructor_body -> branch term := fun i b =>
    (*for inductive type A *)
    (*check that the type of an arg is of form: _ -> _-> _-> A*)
    let fix check_type (t:term) (n:Nat.t): bool :=
      match t with
      | tProd _ _ t => check_type t (n+1)
      | tRel i => if eqb i n then true else false
      | _ => false
      end in
    let fix transformer (t:term) (u:term) (n:Nat.t):=
      let fix lift (t:term) :term :=
        match t with
        | tRel i => tRel (i+1)
        | tApp t1 tl => tApp (lift t1) (map lift tl)
        | _ => todo
        end
      in
      match t with
      | tProd _ t1 t2 => tLambda the_name t1 (transformer t2 (tApp (lift u) [tRel 0]) n)
      | tRel i => tApp (tRel (i+n)) [u]
      | _ => todo
      end in

    {| bcontext := map (fun c : context_decl => the_name) b.(cstr_args) ;
       bbody :=
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
              b.(cstr_args)))
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

(* Compute $unquote (GenerateIdentity_recursive (thisfile, "nat0") input3). *)


Inductive nat':=
| zero' | S' (n m : nat') | newS (k:nat) | S'' (n:Type) (m:n).
Definition input4 := ($run (tmQuoteInductive (thisfile, "nat'"))).
(* Print input4. *)
Compute $unquote (GenerateIdentity_recursive (thisfile, "nat'") input4).



Inductive term2 : Type :=
| Var2 (n:nat)
| App (t1 t2:term2)
| Lam (f: nat-> term2)
| Lam2 (f1: list nat -> term2) (f2:nat -> nat' -> term2) (n:nat)
.
Definition input_term2 := ($run (tmQuoteInductive (thisfile, "term2"))).
Compute $unquote (GenerateIdentity_recursive (thisfile, "term2") input_term2).




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








Record extrainfo:Set := mkinfo
  {
    id_index0: nat;
    id_index1: nat;

    index_param: nat;
    index_arg: nat;

    offset_param : nat;
    offset_arg : nat
  }.

Definition geti (extrainfo:extrainfo) (i:nat) :=
  if leb extrainfo.(index_param) i then extrainfo.(offset_param) + i
  else if leb extrainfo.(index_arg) i then extrainfo.(offset_arg)  + i
  else i.

Definition is_recursive_call (extrainfo:extrainfo) (i:nat) :=
  leb extrainfo.(id_index0) i && leb i extrainfo.(id_index1).


Definition update2 (extrainfo:extrainfo) :=
  mkinfo (extrainfo.(id_index0) - 1)
    (extrainfo.(id_index1) - 1)
    (extrainfo.(index_param) - 1)
    (extrainfo.(index_arg))
    (extrainfo.(offset_param) + 1 )
    (extrainfo.(offset_arg) + 1 )
    .


Definition update3 (extrainfo:extrainfo) :=
  mkinfo (extrainfo.(id_index0) + 1)
    (extrainfo.(id_index1) + 1)
    (extrainfo.(index_param) + 1)
    (extrainfo.(index_arg) + 1 )
    (extrainfo.(offset_param) )
    (extrainfo.(offset_arg) )
    .



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
          let narg := b.(cstr_arity) in
          let index_param := b.(cstr_arity) + ty.(ind_npars) in

          (*extra info at the position of the last argument*)
          let extrainfo := mkinfo
            (index_param-1+0) (index_param-1+n_inductives-1+0)
            (narg-1+0) (0)
            (1 - 0 + 1 + length indices )
            (1 - 0 )
          in


          (*Take Vector.t for example,
              Inductive vec (X:Type) : nat -> Set :=
                ...
                vcons (x:X) (n:nat) (v:vec X n) -> vec X (S n)
                ...

              generate an id_vec:

              Fixpoint id_vec (X:Type) (n;nat) (v:Vec X n) :=
                match v with
                ...
                | vcons x n v => vcons x n (id_vec X n v)
                ...
          *)

            tApp
              (*the type constructor*) (*vcons*)
              (tConstruct the_inductive i Instance.empty)
                (*the type parameters*) (*X*)
                ((plus' (1 + b.(cstr_arity)) seq_param)
                  ++
                 (rev
                   (let fix auxarg extrainfo i args :=
                      match args with
                      | arg :: args =>
                        (match arg.(decl_type) with
                          (*type with indice/parameter*)
                          | tApp (tRel j) tl =>
                            if  is_recursive_call extrainfo j
                            then
                              tApp
                                (*recursive call of the identity function*) (*id_vec*)
                                (tRel (geti extrainfo j))
                                (*the parameter/indice of the identity function*) (*X n*)
                                ((map
                                  (fix Ffix (t:term) : term :=
                                    match t with
                                    | tRel k => tRel (geti extrainfo k)
                                    | tApp tx tl => tApp (Ffix tx) (map Ffix tl)
                                    | _ => t (* todo *)
                                    end) tl)
                                    (*the last argument*) (*v*)
                                  ++ [tRel i])
                            else tRel i
                          (*type without indice/parameter*)
                          | tRel j =>
                            if is_recursive_call extrainfo j
                            then
                              tApp (tRel (geti extrainfo j)) [tRel i]
                            else tRel i
                          (*constructor with lambda type argument*)
                          | tProd _ t1 t2 =>
                            (***********)
                            (*for lambda type argument*)
                            let fix check_type (t:term) (n1 n2:Nat.t): Datatypes.bool :=
                              match t with
                              | tProd _ _ t => check_type t (n1+1) (n2+1)
                              | tRel i => (leb n1 i) && (leb i n2)
                              | tApp (tRel i) _ => (leb n1 i) &&  (leb i n2)
                              | _ => Datatypes.false
                              end in
                            let fix transformer (t:term) (u:term) extrainfo:=
                              let fix lift (t:term) :term :=
                                match t with
                                | tRel i => tRel (i+1)
                                | tApp t tl => tApp (lift t) (map lift tl)
                                | _ => todo
                                end
                              in
                              let fix smt extrainfo t:=
                                match t with
                                | tRel i => tRel (geti extrainfo i)
                                | tApp t tl => tApp (smt extrainfo t) (map (smt extrainfo) tl)
                                | tLambda name t1 t2 => tLambda name (smt extrainfo t1) (smt (update3 extrainfo) t2)
                                | _ => t
                                end
                              in
                              match t with
                              | tProd _ t1 t2 =>
                                tLambda the_name (smt extrainfo t1)
                                  (transformer t2 (tApp (lift u) [tRel 0]) (update3 extrainfo))
                              | tApp (tRel j) tl =>
                                  tApp (tRel (geti extrainfo j))
                                    (((map
                                          (fix Ffix (t:term) : term :=
                                            match t with
                                            | tRel k => tRel (geti extrainfo k)
                                            | tApp tx tl => tApp (Ffix tx) (map Ffix tl)
                                            | _ => t
                                            end) tl))
                                    ++ [u])
                              | tRel i => tApp (tRel (geti extrainfo i)) [u] (*called only when check_type is true*)
                              | _ => todo
                              end in
                            (***********)
                            if (check_type t2 (1+extrainfo.(id_index0)) (1+extrainfo.(id_index1)))
                            then
                              transformer arg.(decl_type) (tRel i) extrainfo
                            else tRel i
                          | _ => tRel i end) :: auxarg (update2 extrainfo) (i+1) args
                      | _ => [] end
                    in
                    auxarg extrainfo 0 b.(cstr_args))
                  )
                )
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




(*with both parameter and indice*)
Inductive vec (X:Type) : nat -> Type:=
  | vnil : vec X O
  | vcons : X -> forall n:nat, vec X n -> vec X (S n).
Definition input_vec := ($run (tmQuoteInductive (thisfile, "vec"))).
Compute $unquote (GenerateIdentity_param (thisfile, "vec") input_vec).



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


(*type constructor with lambda argument*)
Inductive Acc (A : Type) (R : A -> A -> Type) (x : A) : Type :=
	Acc_intro  :(forall y : A, R y x -> Acc A R y) -> Acc A R x.
Definition inputacc := ($run (tmQuoteInductive (thisfile, "Acc"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Acc") inputacc).


Inductive vec' (X:Type) : nat -> Type:=
  | vnil' : vec' X O
  | vcons' : X -> forall n:nat, (nat -> vec' X n) -> nat -> vec' X (S n)
  .
Definition input_vec' := ($run (tmQuoteInductive (thisfile, "vec'"))).
(* Print input_vec'. *)
Compute $unquote (GenerateIdentity_param (thisfile, "vec'") input_vec').


Inductive Point : Type :=
  | Pt : Config -> Config -> Point
with Line : Type :=
  | Ln : Point -> Point -> Line
  | Ext : Line -> Line
with Circle : Type :=
  | Crc : Point -> (nat -> Line) -> Figure-> Circle
with Figure : Type :=
  | P : Point -> Figure
  | L : Line -> Figure
  | C : (nat -> Circle) -> Figure
with Config : Type :=
  | Conf : list Figure -> Config
with R : nat -> Type := R0 : R O | Rs: forall n, Point -> R n -> R (S n)
with R' :Set := R's : forall n, R n -> R'
.
Definition inputpoint := ($run (tmQuoteInductive (thisfile, "Point"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Point") inputpoint).


Inductive ntree3 (A:Set) : nat -> Set :=
  nnode3 (a:A) (n:nat) : (nat -> nforest3 A) -> nat -> ntree3 A n
with nforest3 (A:Set) : Set :=
  | nnil3: nforest3 A
  | ncons3 (n:nat) (_:nat -> ntree3 A n) (_:nforest3 A): nforest3 A
.
Definition inputtree3 := ($run (tmQuoteInductive (thisfile, "ntree3"))).
Compute $unquote (GenerateIdentity_param (thisfile, "ntree3") inputtree3).


(*the result of previous examples still correct*)
Compute $unquote (GenerateIdentity_param (thisfile, "three") input2).


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
(* Inductive vec (X:Type) : nat -> Type:=
  | vnil : vec X O
  | vcons : X -> forall n:nat, vec X n -> vec X (S n).
Definition input_vec := ($run (tmQuoteInductive (thisfile, "vec"))).
Compute $unquote (GenerateIdentity_param (thisfile, "vec") input_vec). *)


Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l').
Definition input_all2 := ($run (tmQuoteInductive (thisfile, "All2"))).
Compute $unquote (GenerateIdentity_param (thisfile, "All2") input_all2).



(* Inductive Point : Type :=
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
  | Conf : list Figure -> Config
.
Definition inputpoint := ($run (tmQuoteInductive (thisfile, "Point"))).
Compute $unquote (GenerateIdentity_param (thisfile, "Point") inputpoint). *)



