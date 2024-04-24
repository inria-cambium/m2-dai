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

Fixpoint listmake {X:Type} (x:X) (n:Datatypes.nat) :=
  match n with
  | Datatypes.O => []
  | Datatypes.S n => cons x (listmake x n) end.

Definition mkdeclnat a b (n:nat) := mkdecl a b n.

Definition plus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+1)) l.

Definition plus_k_index (l: list (BasicAst.context_decl nat)) k :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+k)) l.

Definition minus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)-1)) l.

(*
- generalise extrainfo with arbitary information that can be dynamically looked up
- fancy lambda, fancy it lambda, fancy case, fancy app, etc (kind of monadically passing around the extrainfo like state)
- print context
*)

Inductive information : Type :=
| information_list (na : string) (l : list (BasicAst.context_decl nat))
| information_nat (na : string) (n : nat).

Definition lookup_list (l : list information) (na : string) : list (BasicAst.context_decl nat) :=
  match find (fun i => match i with
                      | information_list na' li => String.eqb na na'
                    | information_nat na' n => String.eqb na na'
              end) l  with
    Some (information_list na l) => l
  | _ => todo
  end.

Definition lookup_item (l : list information) (na : string) : nat :=
  match find (fun i => match i with
  | information_list na' li => String.eqb na na'
  | information_nat na' n => String.eqb na na'
  end) l  with
  Some (information_nat na n) => n
  | _ => todo
  end.

(* Fixpoint replace_info (info:list information) (na:string)  (l : list (BasicAst.context_decl nat)) :=
  match info with
  | (information_list s l0) :: info' =>
      if String.eqb s na then (information_list na l) :: info'
      else (information_list s l0) :: (replace_info info' na l)
  | h :: info' => h :: (replace_info info' na l)
  | _ => todo
  end. *)

(* Inductive  *)

Record extrainfo_gen : Type := mkinfo_gen {
  renaming_gen : list (BasicAst.context_decl nat);

  info : list information ;
  (*may need to distinguish the "type side" and "function side"*)
  (*                            read context    write context *)
}.

Definition empty_info := {|
  renaming_gen := [];
  info := []
|}.

Definition add_listinfo e na l :=
  mkinfo_gen e.(renaming_gen) ((information_list na l)::e.(info)).

Definition add_T (e:extrainfo_gen) ind_bodies : extrainfo_gen :=
  let ind_names := map (
    fun ind_body => {| binder_name := nNamed (ind_body.(ind_name));
                        binder_relevance := Relevant  |}
    ) ind_bodies in
  let l:= mapi (fun i x => mkdeclnat x None i) ind_names in
  add_listinfo e "rels_of_T" l.
  (* mkinfo_gen e.(renaming_gen) ((information_list "rels_of_T" l)::e.(info)). *)

Definition add_id (e:extrainfo_gen) : extrainfo_gen :=
  add_listinfo e "rels_of_id"
    (mapi (fun i _ => mkdeclnat
            {| binder_name:=nNamed "id"; binder_relevance:=Relevant|}
            None i)
      (lookup_list e.(info) "rels_of_T")).
  (* in
  mkinfo_gen e.(renaming_gen) ((information_list "rels_of_id" l)::e.(info)). *)

Definition add_params (e : extrainfo_gen) (ctx : context): extrainfo_gen :=
  let params:= mapi (fun i x => mkdeclnat x.(decl_name) None i) ctx in
  let renaming_gen := params ++ (plus_k_index e.(renaming_gen) (length params)) in
  let info_new := map (
    fun x => match x with
    | information_list na l => information_list na (plus_k_index l (length params))
    | information_nat na n => information_nat na (n + length params) end
    ) e.(info) in
  mkinfo_gen renaming_gen ((information_list "params" params) :: info_new).

Definition add_indices (e : extrainfo_gen) (ctx : context): extrainfo_gen :=
  let indices := mapi (fun i x => mkdeclnat x.(decl_name) None i) ctx in
  let renaming_gen := (plus_k_index e.(renaming_gen) (length indices)) in
  let info := e.(info) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb na "rels_of_T" then x else
        information_list na (plus_k_index l (length indices))
    | information_nat na n => information_nat na (n + length indices) end
  ) info in
  mkinfo_gen renaming_gen ((information_list "indices" indices) :: info_new).

Definition fancy_it_mkProd_or_LetIn (ctx:context) (na:string) (e:extrainfo_gen) (t: extrainfo_gen -> term) : term :=
  if String.eqb na "params" then
    let e' := add_params e ctx in
    it_mkProd_or_LetIn ctx (t e')

    else if String.eqb na "indices" then
      let e' := add_indices e ctx in
      it_mkProd_or_LetIn ctx (t e')
    else todo
  .

(*not general enough... bad*)
Definition fancy_tProd na e (t1:extrainfo_gen -> term) (t2:extrainfo_gen -> term) :=
  let update0 (e:extrainfo_gen) : extrainfo_gen :=
    let renaming_gen := e.(renaming_gen) in
    let info := e.(info) in
    let info_new := map (
      fun x => match x with
      | information_list na l => information_list na (plus_one_index l)
      | information_nat na n => information_nat na (1 + n) end
    ) info in
    let renaming_new := plus_one_index renaming_gen in
    mkinfo_gen renaming_new info_new
  in
  tProd na (t1 e) (t2 (update0 e)).

Definition fancy_it_mkLambda_or_LetIn (ctx:context) (na:string) (e:extrainfo_gen) (t: extrainfo_gen -> term) : term :=
  if String.eqb na "params" then
    let e' := add_params e ctx in
    it_mkLambda_or_LetIn ctx (t e')

    else if String.eqb na "indices" then
      let e' := add_indices e ctx in
      it_mkLambda_or_LetIn ctx (t e')
    else todo
  .

(*not general enough... bad*)
(*for lambda term only appear in the function generated*)
Definition update_lambda_f na (e:extrainfo_gen) : extrainfo_gen :=
  let renaming_gen := e.(renaming_gen) in
  let info := e.(info) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb na "rels_of_T" then x else
        information_list na (plus_one_index l)
    | information_nat na n => information_nat na (1 + n) end
  ) info in
  let renaming_new := plus_one_index renaming_gen in
  let name := match na.(binder_name) with
    | nAnon => "var_lambda"
    | nNamed s => s end in
  let var := information_nat name 0 in
  mkinfo_gen renaming_new (var :: info_new).

(*for lambda term appear in the type definition*)
Definition update_lambda_type_arg (na:aname) (e:extrainfo_gen) :=
  let renaming_gen :=
    (mkdeclnat na None 0)
    :: (plus_one_index e.(renaming_gen))
  in
  mkinfo_gen renaming_gen
    (
      map (
        fun x => match x with
        | information_list na l => information_list na (plus_one_index l)
        | information_nat na n => information_nat na (1 + n) end
      ) e.(info)
    )
  .

Definition fancy_tLambda na (e:extrainfo_gen) (t1:extrainfo_gen -> term)
  (update:aname -> extrainfo_gen -> extrainfo_gen) (t2:extrainfo_gen -> term)
  : term :=
  tLambda na (t1 e) (t2 (update na e)).

Definition fancy_tCase (e:extrainfo_gen) t0 t1 t2 t3 t4 t5 t6 t7 (t8:extrainfo_gen -> list (branch term)):term :=
  let pcontext := t5 e in
  (*very limited*)
  let update_pcontext pcontext e :=
    let renaming_gen := e.(renaming_gen) in
    let info := e.(info) in
    let info_new := map (
      fun x => match x with
      | information_list na l => information_list na (plus_k_index l (length pcontext))
      | information_nat na n => information_nat na (n + length pcontext) end
    ) info in
    (*very limited*)
    let l:= mapi (fun i x => mkdeclnat x None (i+1)) (tl pcontext) in
    let renaming_new := plus_k_index renaming_gen (length pcontext) in
    let info_new := (information_list "pcontext_indices" l) :: info_new in
    mkinfo_gen renaming_new info_new
  in
  tCase
    {|
      ci_ind := t0 e ;
      ci_npar := t1 e;
      ci_relevance := t2 e
   |}
  {|
    puinst := t3 e;
    pparams := t4 e;
    pcontext := pcontext;
    preturn := t6 (update_pcontext pcontext e)
  |}
  (t7 e) (t8 e).

Definition add_args (e:extrainfo_gen) (ctx: context): extrainfo_gen :=
  let nargs := length ctx in
  (* let l:= mapi (fun i x => mkdeclnat x.(decl_name) None i) ctx in
  let renaming_gen := l ++ (plus_k_index e.(renaming_gen) (nargs)) in *)
  let l:= mapi (fun i x => mkdeclnat x.(decl_name) None i) (ctx) in
  (*start with the last argument*)
  let renaming_gen := (tl l) ++ (plus_k_index e.(renaming_gen) (nargs)) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb "rels_of_T" na  then
          information_list na (plus_k_index l (nargs-1))
        else
          information_list na (plus_k_index l nargs)
    | information_nat na n => information_nat na (n + nargs) end
    ) e.(info) in
  let arg := information_nat "arg_current" 0 in
  mkinfo_gen (renaming_gen) (arg:: info_new).

Definition update_ctr_arg_back (e:extrainfo_gen) : extrainfo_gen :=
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb "rels_of_T" na then
          information_list na (minus_one_index l)
        else x
    | information_nat na n =>
        if String.eqb "arg_current" na then information_nat na (n + 1)
        else x end
  ) e.(info) in
  mkinfo_gen (tl e.(renaming_gen)) info_new
.

Definition map_with_extrainfo_gen {X Y:Type} (f:X -> extrainfo_gen -> Y) (l:list X)
  (e:extrainfo_gen) (update:extrainfo_gen -> extrainfo_gen):=
  let fix Ffix f l e update:=
    match l with
    | x :: l => (f x e) :: (Ffix f l (update e) update)
    | _ => []
    end
  in
  Ffix f l e update.

Definition geti_gen (e:extrainfo_gen) (i:nat) :=
  let l := map (fun x => x.(decl_type)) e.(renaming_gen) in
  tRel (nth i l todo).

Definition get_id_gen (e:extrainfo_gen) (i:nat) :=
  let l := lookup_list e.(info) "rels_of_id" in
  tRel (nth i l todo).(decl_type).

Definition rels_of (na:string) (e:extrainfo_gen) :=
  let l := lookup_list e.(info) na in
  (**)rev(**) (map (fun x => tRel x.(decl_type)) l).

Definition rel_of (na:string) (e:extrainfo_gen) :=
  let n := lookup_item e.(info) na in
  tRel n.

Definition is_recursive_call_gen (e:extrainfo_gen) i : option nat:=
  let l := map (fun x => x.(decl_type)) (lookup_list e.(info) "rels_of_T") in
  let fix Ffix l j :=
    match l with
    | k :: l0 => if eqb k i then Some j else Ffix l0 (j+1)
      (* if ltb i k then None *)
    | [] => None
  end in
  Ffix l 0.

Definition type_rename_transformer (e:extrainfo_gen) (t:term) : term:=
  let fix Ffix e t :=
    match t with
    | tRel k => geti_gen e k
    | tApp tx tl => tApp (Ffix e tx) (map (Ffix e) tl)
    | tLambda name t1 t2 =>(*tProd ?*) tLambda name (Ffix e t1) (Ffix (update_lambda_type_arg name e) t2)
    | _ => t (* todo *)
  end in
  Ffix e t.


Definition the_name := {| binder_name := nNamed "x";
                  binder_relevance := Relevant  |}.


Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).
Axiom print_context : extrainfo_gen -> forall {A}, A.



Definition GenerateIdentity_param (na : kername) (ty :  mutual_inductive_body) : term :=

  let params := ty.(ind_params) in
  let initial_info := add_id $ add_T empty_info ty.(ind_bodies) in

  let generate_inductive (i:Datatypes.nat) (body: one_inductive_body) :=

    let the_inductive := {| inductive_mind := na; inductive_ind := i |} in
    let indices := body.(ind_indices) in

    let aux : extrainfo_gen -> Nat.t -> constructor_body -> branch term := fun e i b =>
      {| bcontext := map (fun a => a.(decl_name)) b.(cstr_args) ;
         bbody :=
          let e := add_args e b.(cstr_args) in
          let constructor_current := tConstruct the_inductive i Instance.empty in
          tApp
            constructor_current
            ((*the type parameters*) (*X*)
              ((rels_of "params" e))
              ++
              (rev
                (let auxarg arg e:=
                  (*current argument*)
                  let arg_current := rel_of "arg_current" e in

                  match arg.(decl_type) with
                  (*type with indice/parameter*)
                  | tApp (tRel j) tl =>
                    match is_recursive_call_gen e j with
                    | None => arg_current
                    | Some kk =>
                      tApp
                        (*recursive call of the identity function*) (*id_vec*)
                        (get_id_gen e kk)
                        ( (*the parameter/indice of the identity function*) (*X n*)
                          (map (type_rename_transformer e) tl)
                          (*the last argument*) (*v*)
                          ++ [arg_current])
                    end
                  | tRel j =>
                    match is_recursive_call_gen e j with
                    | None => arg_current
                    | Some kk => tApp (get_id_gen e kk) [arg_current]
                    end
                  | tProd _ t1 t2 =>
                    (***********)
                    let fix check_type (t:term) (n1 n2:Nat.t): option nat :=
                      match t with
                      | tProd _ _ t => check_type t (n1+1) (n2+1)
                      | tRel i =>
                        if (leb n1 i) && (leb i n2) then Some (i-n1) else None
                      | tApp (tRel i) _ =>
                        if (leb n1 i) && (leb i n2) then Some (i-n1) else None
                      | _ => None
                      end in
                    let fix transformer (t:term) (u:term) (tid:term) e :=
                      let fix lift (t:term) :term :=
                        match t with
                        | tRel i => tRel (i+1)
                        | tApp t tl => tApp (lift t) (map lift tl)
                        | _ => todo (*impossible to take this branch*)
                        end
                      in
                      match t with
                      | tProd _ t1 t2 =>
                        fancy_tLambda the_name e
                          (fun e => type_rename_transformer e t1)
                          update_lambda_type_arg
                          (fun e =>
                            transformer t2 (tApp (lift u) [tRel 0])
                              (lift tid) e)
                      | tApp (tRel j) tl =>
                          tApp tid
                            ((map (type_rename_transformer e) tl)
                              ++ [u])
                      | tRel _ => tApp tid [u]
                      | _ => todo (* other cases exist? *)
                      end in
                    let l := lookup_list e.(info) "rels_of_T" in
                    let id_index0 := (hd todo l).(decl_type) in
                    let id_index1 := (last l todo).(decl_type) in
                    match check_type t2 (1 + id_index0) (1 + id_index1) with
                    | None => arg_current
                    | Some kk =>
                        transformer arg.(decl_type) arg_current (get_id_gen e kk) e
                    end
                    (***********)
                  | _ => arg_current end
                in
                map_with_extrainfo_gen auxarg b.(cstr_args)
                  (e) update_ctr_arg_back)
              )
            )
      |}
    in

    {|
      dname := {| binder_name := nNamed "id" ;
                  binder_relevance := Relevant |};
      dtype :=
        fancy_it_mkProd_or_LetIn params "params" (initial_info) $
          fun e => fancy_it_mkProd_or_LetIn indices "indices" e $
            fun e =>
              fancy_tProd the_name e
                (fun e => tApp
                  (tInd the_inductive Instance.empty)
                    (rels_of "params" e ++ rels_of "indices" e))

                (fun e => tApp
                  (tInd the_inductive Instance.empty)
                    (rels_of "params" e ++ rels_of "indices" e))
        ;

      dbody :=
        fancy_it_mkLambda_or_LetIn params "params" (initial_info) $
          fun e => fancy_it_mkLambda_or_LetIn indices "indices" e $
            fun e =>
              fancy_tLambda the_name e
                (fun e => tApp (tInd the_inductive Instance.empty)  (rels_of "params" e ++ rels_of "indices" e))
                update_lambda_f
                (fun e =>
                  fancy_tCase e
                    (fun _ => the_inductive)
                    (fun e => length (lookup_list e.(info) "params"))
                    (fun _ => Relevant)
                    (fun _ => [])
                    (fun e => rels_of "params" e)
                    (fun e =>
                      listmake the_name (1 + length (lookup_list e.(info) "indices"))
                     )
                    (fun e =>
                      tApp (tInd the_inductive Instance.empty)
                      ((rels_of "params" e ) ++ (rels_of "pcontext_indices" e)))
                    (fun e => rel_of "x" e)
                    (fun e => mapi (aux e) body.(ind_ctors))
                )
                ;
      rarg := length indices + length params
    |}
  in
  tFix (mapi generate_inductive ty.(ind_bodies)) 0
.


(* Print TemplateMonad. *)

Notation "'$let' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
                                     (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

Notation "'try' '$let' ' x ':=' c1 'in' c2 'else' c3" := (@bind _ _ _ _ c1 (fun y =>
                                                              (match y with x => c2
                                                                       | _ => c3
                                                               end)))
                                         (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

(* MetaCoq Test Quote nat. *)
(* Definition *)(* Eval *)(* Lemma *)(* Instance *)(* Print *)(* Compute *)(* Check *)

Definition generate_identity {A} (a : A) (out : option ident): TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
      let kn := ind.(inductive_mind) in
      $let mind := tmQuoteInductive kn in
      let id := GenerateIdentity_param kn mind in
      $let u := tmUnquote id in
      $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; ret tt
        | None => tmPrint r
        end
    | _ => tmFail "no inductive"
    end.

Notation "'Derive' 'Identity' a 'as' id" := (generate_identity a (Some id)) (at level 0).
Notation "'Print' 'Identity' a" := (generate_identity a None) (at level 0).


Inductive All2 (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
   All2_nil : All2 A B R [] []
   | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                 R x y -> All2 A B R l l' -> All2 A B R (x :: l) (y :: l').
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


(*
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
 *)
