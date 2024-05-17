Require Export MetaCoqPrelude.
Export MCMonadNotation.
Export List.
Export ListNotations.

Axiom todo : forall {A}, A.

Local Definition mkdeclnat a b (n:nat) := mkdecl a b n.

Local Definition plus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+1)) l.

Local Definition plus_k_index (l: list (BasicAst.context_decl nat)) k :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+k)) l.

Local Definition minus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)-1)) l.


Inductive information : Type :=
| information_list (l : list (BasicAst.context_decl nat))
| information_nat (n : nat).

Definition lookup_list (l : list (string * information)) (na : string) : list (BasicAst.context_decl nat) :=
  match find (fun i => match i with
                      | (na', _) => String.eqb na na'
              end) l  with
    Some (_, information_list l) => l
  | _ => []
  end.

Definition lookup_item (l : list (string * information)) (na : string) : nat :=
  match find (fun i => match i with
  | (na', _) => String.eqb na na'
  end) l  with
  Some (_, information_nat n) => n
  | _ => todo
  end.

Local Fixpoint replace_add_info (info:list (string * information)) (na:string) (item : BasicAst.context_decl nat) :=
  match info with
  | (s, information_list l0) :: info' =>
      if String.eqb s na then (s, information_list (item::l0)) :: info'
      else (s, information_list l0) :: (replace_add_info info' na item)
  | h :: info' => h :: (replace_add_info info' na item)
  | [] => (na, information_list [item]) :: []
  end.


(****************************************************************)
(*
  We give an xxx for generating things from the (inductive) type definition.

  ex.
    Inductive type ===> identity function
    Inductive type ===> inductive principle
    Inductive type ===> type of inductive principle

  Source of the generation : type definition
  Target: ......
*)

(* extrainfo: the local information carried during the generation *)

(*renaming:
  A renaming from the source environment (type definition) to the target environment:

  At any point of the generation process,
  the ith (begin with 0th) element of renaming has decl_type j means:
    the (tRel i) in the source environment = (tRel j) in the target environment.

  ex.
    generating the identity function of Vector.t

    Source:
      Inductive vec (A:Type) :nat -> Type := ...
                                      ^
    Target:
      Fixpoint id (A:Type) (n:nat) (v:vec A n) := ...
                                    ^
    When we are at the point to define this v, the parameter (A:Type) and indice (nat) are visited,
    the renaming should be [1]: means that that here (tRel 0) of source should be (tRel 1) in the target, i.e. A

*)
Record extrainfo : Type := mkinfo {
  renaming : list (BasicAst.context_decl nat);
  (*info: to save some useful information (parameters, indices, ...) *)
  info : list (string * information) ;
  kn : kername;
}.



Definition add_listinfo e na l :extrainfo :=
  mkinfo e.(renaming) ((na, information_list l)::e.(info)) e.(kn).

Definition add_info_names (e:extrainfo) (str:string) names : extrainfo :=
  let l:= mapi (fun i x => mkdeclnat x None i) names in
  add_listinfo e str l.

(*Make the initial information.
  By default, we begin with the info which contains only the kername,
  and the list of type names
*)
Definition make_initial_info (kn:kername) (ty:mutual_inductive_body) :extrainfo :=
  let e := mkinfo [] [] kn in
  add_info_names e "rels_of_T"
    (map (fun ind_body => {| binder_name := nNamed (ind_body.(ind_name));
                        binder_relevance := Relevant  |}
          ) ty.(ind_bodies)).

(*The indicator which shows if some new information should be saved
  when new variable introduced *)
Inductive saveinfo:=
  | Savelist (s:string)
  | Saveitem (s:string)
  | NoSave.

Local Definition update_kp (na:aname) (e:extrainfo) (saveinfo:saveinfo):=
  let item := mkdeclnat na None 0 in
  let renaming :=
    item :: (plus_one_index e.(renaming))
  in
  let info :=
    map (
      fun x => match x with
      | (na, information_list l) => (na, information_list (plus_one_index l))
      | (na, information_nat n) => (na, information_nat (1 + n)) end
    ) e.(info)
  in
  match saveinfo with
  | NoSave => mkinfo renaming info e.(kn)
  | Saveitem str => mkinfo renaming ((str, information_nat 0) ::info) e.(kn)
  | Savelist str => mkinfo renaming (replace_add_info info str item) e.(kn)
  end
  .

Local Definition update_mk na (e:extrainfo) (saveinfo:saveinfo) : extrainfo :=
  let info := map (
    fun x => match x with
    | (na, information_list l) =>
        if String.eqb na "rels_of_T" then x else
        (na, information_list (plus_one_index l))
    | (na, information_nat n) => (na, information_nat (1 + n)) end
  ) e.(info) in
  let renaming := plus_one_index e.(renaming) in
  let item := mkdeclnat na None 0 in
  match saveinfo with
  | NoSave => mkinfo renaming info e.(kn)
  | Saveitem str => mkinfo renaming ((str, information_nat 0)::info) e.(kn)
  | Savelist str => mkinfo renaming (replace_add_info info str item) e.(kn)
  end.

Local Definition add_args (e:extrainfo) (ctx: context): extrainfo :=
  let nargs := length ctx in
  let l:= mapi (fun i x => mkdeclnat x.(decl_name) None i) (ctx) in
  (*start with the last argument*)
  let renaming := (tl l) ++ (plus_k_index e.(renaming) (nargs)) in
  let info_new := map (
    fun x => match x with
    | (na, information_list l) =>
        if String.eqb "rels_of_T" na  then
          (na, information_list (plus_k_index l (nargs-1)))
        else
          (na, information_list (plus_k_index l nargs))
    | (na, information_nat n) => (na, information_nat (n + nargs)) end
    ) e.(info) in
  let arg := information_nat 0 in
  mkinfo (renaming) (("arg_current", arg):: info_new) e.(kn).

(* Local Definition add_args' (e:extrainfo) (ctx: context): extrainfo :=
  let nargs := length ctx in
  let renaming := plus_k_index e.(renaming) (nargs) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb "rels_of_T" na then x
        else information_list na (plus_k_index l nargs)
    | information_nat na n => information_nat na (n + nargs) end
    ) e.(info) in
  mkinfo renaming info_new e.(kn).
 *)


Definition fancy_tCase (e:extrainfo) t0 t2 t3 t4 t5 t6 t7 (t8:extrainfo -> list (context * (extrainfo -> term))):term :=
  let pcontext := t5 e in
  let pparams := t4 e in
  (*very limited*)
  let update_pcontext pcontext e :=
    let renaming := e.(renaming) in
    let info := e.(info) in
    let info_new := map (
      fun x => match x with
      | (na, information_list l) => (na, information_list (plus_k_index l (length pcontext)))
      | (na, information_nat n) => (na, information_nat (n + length pcontext)) end
    ) info in
    (*very limited*)
    let l:= mapi (fun i x => mkdeclnat x None (i+1)) (tl pcontext) in
    let renaming_new := plus_k_index renaming (length pcontext) in
    let info_new := ("pcontext_indices", information_list l) :: info_new in
    mkinfo renaming_new info_new e.(kn)
  in
  tCase
    {|
      ci_ind := t0 e ;
      ci_npar := length pparams;
      ci_relevance := t2 e
    |}
  {|
    puinst := t3 e;
    pparams := pparams;
    pcontext := pcontext;
    preturn := t6 (update_pcontext pcontext e)
  |}
  (t7 e)
  (map
    (fun '(c, t) =>
      {| bcontext := map decl_name c;
         bbody := t (add_args e c) |})
    (t8 e)).

Local Definition update_ctr_arg_back (e:extrainfo) : extrainfo :=
  let info_new := map (
    fun x => match x with
    | (na, information_list l) =>
        if String.eqb "rels_of_T" na then
          (na, information_list (minus_one_index l))
        else x
    | (na, information_nat n) =>
        if String.eqb "arg_current" na then (na, information_nat (n + 1))
        else x end
  ) e.(info) in
  mkinfo (tl e.(renaming)) info_new e.(kn)
.

(* Search "length" "fold". *)
(* Local Definition update_ctr_arg' (e:extrainfo) : extrainfo := todo
.

Definition handle_arg (arg:context_decl)
  (f:context_decl->extrainfo->term->term)
  (e:extrainfo) (t:extrainfo->term): term :=
  f arg e (t (update_ctr_arg' e)).

Fixpoint fold_arg {X} (args:context) (f:context_decl->extrainfo-> X -> X)
  (e:extrainfo) (t: extrainfo -> X): X :=
  match args with
  | [] => t e
  | arg :: l => f arg e (fold_arg l f (update_ctr_arg' e) t)
  end.

Definition map_with_info_arg' (f:context_decl -> extrainfo -> term)
  (l:context) (e:extrainfo): list term:=
  fold_arg l (
    fun arg tl =>
      (f arg e) :: tl
  ) e (fun _ => []).

Definition auxarg (arg:context_decl) (e:extrainfo) : term := todo.

Definition testmyf (b:constructor_body) (e:extrainfo): list term :=
  map_with_info_arg' auxarg (rev b.(cstr_args)) e.
*)


(*Used only when tCase, match with ..., to be explained *)
Definition map_with_extrainfo_arg {X Y:Type} (f:X -> extrainfo -> Y) (l:list X)
  (e:extrainfo) :=
  let fix Ffix f l e:=
    match l with
    | x :: l => (f x e) :: (Ffix f l (update_ctr_arg_back e))
    | _ => []
    end
  in
  Ffix f l e.

Local Definition findi (x:nat) (l:list nat):=
  let fix Ffix x l n:=
    match l with
    | [] => None
    | y :: l' => if eqb y x then Some n else Ffix x l' (n+1)
    end
  in
  Ffix x l 0.

(*
  Used for lambda type argument. To be explained
*)
Definition check_return_type (t:term) (e:extrainfo) : option nat :=
  let fix Ffix t e {struct t}:=
    match t with
    | tRel i =>
      let types := lookup_list e.(info) "rels_of_T" in
      let types := map decl_type types in
      findi i types
    | tApp t _ => Ffix t e
    | tProd name _  t2 => Ffix t2 (update_kp name e NoSave)
    | _ => None
    end in
  Ffix t e.



(****************************************************************)
(*return the tRel term of the [i]th element of the [e.(renaming)] *)
Definition geti_rename (e:extrainfo) (i:nat) :=
  let l := map (fun x => x.(decl_type)) e.(renaming) in
  tRel (nth i l todo).

(*return the tRel term of the [i]th element of the information list named [na] inside [e.(info)] *)
Definition geti_info (na:string) (e:extrainfo) (i:nat) :=
  let l := lookup_list e.(info) na in
  tRel (nth i l todo).(decl_type).

(*return the reversal tRel term list of the information list named [na] of [e]*)
Definition rels_of (na:string) (e:extrainfo) :=
  let l := lookup_list e.(info) na in
  (**)rev(**) (map (fun x => tRel x.(decl_type)) l).

(*return the tRel term of the informationitem named [na] of [e]*)
Definition rel_of (na:string) (e:extrainfo) :=
  let n := lookup_item e.(info) na in
  tRel n.

(* In the type definition, (mutual inductive, maybe n different inductive bodies)
   check if the debruijn index [i] refer to a type (being defined),
   if yes, return its reverse order.

   ex.
    Inductive ntree (A:Set) : Set :=
      nnode : A -> nforest A -> ntree A
                   ^^^^^^^
    with nforest (A:Set) : Set := ...

    when we use the function below to check this `nforest`, it should return `Some 0`.
*)
Definition is_recursive_call_gen (e:extrainfo) i : option nat:=
  let l := map (fun x => x.(decl_type)) (lookup_list e.(info) "rels_of_T") in
  let fix Ffix l j :=
    match l with
    | k :: l0 => if eqb k i then Some j else Ffix l0 (j+1)
      (* if ltb i k then None *)
    | [] => None
  end in
  Ffix l 0.

(* Transform the `type term` in the source
          to the `type term` in the target
*)
Definition type_rename_transformer (e:extrainfo) (t:term) : term:=
  let n_ind := length (lookup_list e.(info) "rels_of_T") in
  let fix Ffix e t :=
    match t with
    | tRel k =>
      match is_recursive_call_gen e k with
      | Some i => tInd {| inductive_mind :=e.(kn); inductive_ind := n_ind - i - 1 |} []
      | None => geti_rename e k
      end
    | tApp tx tl => tApp (Ffix e tx) (map (Ffix e) tl)
    | tLambda name t1 t2 => tLambda name (Ffix e t1) (Ffix (update_kp name e NoSave) t2)
    | tProd na t1 t2 => tProd na (Ffix e t1) (Ffix (update_kp na e NoSave) t2)
    | _ => t (* todo *)
  end in
  Ffix e t.

(* Introduce a Prod in the target, introduce a new variable that could be referenced *)
(* [saveinfo]: if save the information of this new variable into e
   [na]:       the aname of the new variable
   [e]:        the local information
   [t1]:       the type of new variable (need to be fed with extrainfo)
   [t2]:       the term (need to be fed with extrainfo)
*)
Definition mktProd (saveinfo:saveinfo) na e (t1:term) (t2:extrainfo -> term) :=
  let e' := update_mk na e saveinfo in
  tProd na (t1) (t2 e').

(* Consume a Prod of the source, introduce it in the target *)
Definition kptProd (saveinfo:saveinfo) na e (t1:term) (t2:extrainfo -> term) :=
  let e' := update_kp na e saveinfo in
  tProd na (t1) (t2 e').

(*iterate kptProd*)
Definition it_kptProd (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
        Ffix ctx' e (
          fun e =>
            kptProd saveinfo decl.(decl_name) e
              (type_rename_transformer e decl.(decl_type))
              t
        )
  end in
  Ffix ctx e t.


(*iterate mktProd*)
Definition it_mktProd (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e e0 t:=
    match ctx with
    | [] => t e e0
    | decl :: ctx' =>
        Ffix ctx' e e0 (fun e e0 =>
          let e' := update_kp decl.(decl_name) e saveinfo in
          let e0 := update_mk decl.(decl_name) e0 saveinfo in
          tProd decl.(decl_name)
            (type_rename_transformer e decl.(decl_type)) (t e' e0)
        )
  end in
  Ffix ctx e e (fun (_:extrainfo) => t).


(* How to choose [mktProd] [kptProd]:

  Source: inductive type definition
    Inductive T (A1:Param1) ... (Ak:Paramk): Ind1 -> Ind2 ...  ->Indm -> Type := ... .

  [kptProd] uses [update_kp], [update_mk] uses [update_mk]

  [update_kp] changes the information of "rels_of_T", add one new renamed item into the shifted renaming list
  [update_mk] does not change the information of "rels_of_T", just shift the renaming list

  When creating a Prod in the target,
  use [kptProd saveinfo na e t1 t2] if [na] refers to a term that could be referenced to (by tRel _) in the source
  use [mktProd] otherwise.

  ex. for the type definitin above,
    (A1, ... Ak) can be referenced in the source, so we use [kptProd]
    (Ind1,..., Indm) can not be referenced in the source, so use [mktProd]
*)


(* Introduce a Lambda in the target *)
Definition mktLambda saveinfo na (e:extrainfo)  (t1:term)
  (t2:extrainfo -> term)
  : term :=
  tLambda na (t1) (t2 (update_mk na e saveinfo)).

(* Consume a Prod of the source, introduce it in the target *)
Definition kptLambda saveinfo na (e:extrainfo) (t1:term)
  (t2:extrainfo -> term)
  : term :=
  tLambda na (t1) (t2 (update_kp na e saveinfo)).

(*iterate mktLambda*)
Definition it_mktLambda saveinfo (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e e0 t:=
    match ctx with
    | [] => t e e0
    | decl :: ctx' =>
        Ffix ctx' e e0 (fun e e0 =>
          let e' := update_kp decl.(decl_name) e saveinfo in
          let e0 := update_mk decl.(decl_name) e0 saveinfo in
          tLambda decl.(decl_name)
            (type_rename_transformer e decl.(decl_type)) (t e' e0)
        )
  end in
  Ffix ctx e e (fun (_:extrainfo) => t).

(*iterate kptLambda*)
Definition it_kptLambda saveinfo (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
        Ffix ctx' e (
          fun e =>
            kptLambda saveinfo decl.(decl_name) e
              (type_rename_transformer e decl.(decl_type))
              t
        )
  end in
  Ffix ctx e t.





(****************************************************************)
(*If just need to get information from the source
  no need to generate term, use functions below
*)

Definition update_kp_util {Y:Type} saveinfo na e
  (t1:extrainfo -> Y -> Y) (acc:extrainfo -> Y) :Y :=
  let e' := update_kp na e saveinfo in
  (t1 e) (acc e').

Definition fold_update_kp_util {Y:Type} saveinfo (ctx:context) (e:extrainfo)
  (t0:extrainfo -> Y -> Y) (acc: extrainfo -> Y) :Y :=
  let fix Ffix ctx e acc:=
    match ctx with
    | [] => acc e
    | decl :: ctx' =>
        Ffix ctx' e (
          fun e =>
            update_kp_util saveinfo decl.(decl_name) e t0 acc
        )
  end in
  Ffix ctx e acc.


Axiom print_info: extrainfo -> forall {A}, A.

(* Definition skipvar (e:extrainfo) (decl:context_decl): extrainfo :=
  let item := mkdeclnat decl.(decl_name) None todo in
  let renaming := item :: (plus_one_index e.(renaming)) in
  let info := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb na "rels_of_T" then
          information_list na (plus_one_index l)
        else x
    | information_nat na n => x end
  ) e.(info) in
  mkinfo renaming info e.(kn). *)

(* try *)
(*
Definition update0 (saveinfo:saveinfo) (na:aname) e :extrainfo :=
  let info := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb na "rels_of_T" then
          information_list na (plus_one_index l)
        else x
    | information_nat na n => information_nat na n end
  ) e.(info) in
  let renaming := plus_one_index e.(renaming) in
  let item := mkdeclnat na None 0 in
  match saveinfo with
  | NoSave => mkinfo renaming info e.(kn)
  | Saveitem str => mkinfo renaming ((information_nat str 0)::info) e.(kn)
  | Savelist str => mkinfo renaming (replace_add_info info str item) e.(kn)
  end.


Print context.

Definition it_new (saveinfo:saveinfo) (ctx:context) e (t:extrainfo  -> context_decl -> term -> term) (acc:extrainfo -> term) :=
  let fix Ffix ctx e :=
    match ctx with
    | [] => acc e
    | decl :: ctx' =>
      let e' := update0 saveinfo decl.(decl_name) e in
      t e decl (Ffix ctx' e')
    end in
  Ffix ctx e. *)

(*
  it_new (Savelist "params") params initial_info
    (fun e decl t =>
      (*
        if "is uniform param" then tProd _ (type_rename_transformer e decl.(decl_type)) t
        else
      *)
    )
    (fun e =>
    )
*)