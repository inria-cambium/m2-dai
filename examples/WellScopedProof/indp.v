Require Import MetaCoq.Programming.
Require Import WellScopedProof.api_change.
Global Open Scope bs.

(*
  derive the type of induction principle of any inductive type

  1. mutual inductive types are not concerned
  2. cannot handle lambda-type-argument, (will derive a naive indp)
     e.g.
      Inductive myterm : Type :=
        | mylam : (nat -> myterm) -> myterm.

      The result derived of the type above will be
        forall (P:myterm -> Prop),
          (forall (x:nat -> myterm), P (mylam x)) ->
          forall (x:myterm), P x.
*)

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.

Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.


Definition auxarg arg the_inductive (params:context) (t:infolocal -> term) :infolocal -> term :=
  let t1 := arg.(decl_type) in
  let na := arg.(decl_name) in
  fun e =>
    match t1 with
    | tRel i =>
      match is_rec_call e i with
      | Some _ =>
        e <- mktProd (Savelist "args") e na (tInd the_inductive []);;
        kptProd NoSave e the_name
          (tApp (rel_of "P" e) [get_info_last "args" e (*tRel 0*)])
          t
      | None =>
        kptProd (Savelist "args") e na
          (mapt e t1)
          t
      end
    | tApp (tRel i) tl =>
      match is_rec_call e i with
      | Some _ =>
        e <-
          mktProd (Savelist "args") e na
            (tApp (tInd the_inductive []) (map (mapt e) tl));;
        kptProd NoSave e the_name
          (tApp
            (rel_of "P" e)
            (let tl := n_tl tl (length params) in
              (map (mapt e) tl) (*n*) ++ [get_info_last "args" e (*tRel 0*)] (*v*))
          ) t
      | None =>
        kptProd (Savelist "args") e na
          (mapt e t1)
          t
      end
    (**********************)
    | tProd na _ _ =>
      kptProd (Savelist "args") e na
        (mapt e t1)
        t
    (**********************)
    | _ => kptProd (Savelist "args") e na
            (mapt e t1)
            t
    end.

Definition transformer_result cstrindices constructor_current :infolocal -> term := fun e =>
  tApp (rel_of "P" e)
    (
      (map (mapt e) cstrindices)
      ++
      [tApp constructor_current
        (rels_of "params" e ++ rels_of "args" e)]
    ).

Fixpoint Ffix_args the_inductive params args t :=
  match args with
  | [] => t
  | a :: args' => Ffix_args the_inductive params args'(auxarg a the_inductive params t)
  end.

Definition auxctr (i:nat) (ctr:constructor_body) the_inductive params : infolocal -> term :=
  let constructor_current := tConstruct the_inductive i [] in
  let cstr_type := ctr.(cstr_type) in
  Ffix_args the_inductive params ctr.(cstr_args)
    (transformer_result ctr.(cstr_indices) constructor_current).

(* Fixpoint Ffix_ctrs i the_inductive params b t : infolocal -> term :=
  match b with
  | [] => t
  | a :: b' =>
    Ffix_ctrs (S i) the_inductive params b' (
      fun e => mktProd NoSave e the_name (auxctr (#|b| - i - 1) a the_inductive params (add_emp_info e (Some "args"))) t
    )
  end. *)

Fixpoint Ffix_ctrs' i the_inductive params b t : infolocal -> term := fun e =>
  match b with
  | [] => t e
  | a :: b' =>
    mktProd NoSave e the_name (auxctr i a the_inductive params (add_emp_info e (Some "args")))
     (Ffix_ctrs' (S i) the_inductive params b' t)
  end.

Definition aux b the_inductive params e t :=
  Ffix_ctrs' 0 the_inductive params b t e.


Definition GenerateIndp (na : kername) (ty : mutual_inductive_body) : term :=
  let params := ty.(ind_params) in
  let initial_info :=  make_initial_info na ty in
  let body := hd todo ty.(ind_bodies) in
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let indices := body.(ind_indices) in

  e <- it_kptProd_default (Some "params") initial_info params;;
  e <- mktProd (Saveitem "P") e prop_name
        (
          e <- it_mktProd_default (Some "indices") e indices;;
          tProd the_name
            (tApp (tInd the_inductive [])
              (rels_of "params" e
                ++ rels_of "indices" e)
            )
            (tSort sProp)
        );;
  e <- aux (body.(ind_ctors)) the_inductive params e;;
    e <- it_mktProd_default (Some "indices") e (indices);;
    e <- mktProd (Saveitem "x") e the_name
          (tApp (tInd the_inductive [])
              (rels_of "params" e ++ rels_of "indices" e)
            );;
    (tApp (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
  .


Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

Definition generate_indp {A} (a : A) (out : option ident): TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
      let kn := ind.(inductive_mind) in
      $let mind := tmQuoteInductive kn in
      let id := GenerateIndp kn mind in
      $let u := tmUnquote id in
      $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; tmPrint r ;; ret tt
        | None => tmPrint r
        end
    | _ => tmFail "no inductive"
    end.

Notation "'Derive' 'InductivePrinciple' a 'as' id" := (generate_indp a (Some id)) (at level 0).
