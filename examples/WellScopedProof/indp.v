Require Import MetaCoq.Programming.
Require Import WellScopedProof.api_change.
Global Open Scope bs.

(*
  derive the type of induction principle of any inductive type
    - can handle mutual inductive type
    - cannot handle lambda-type-argument, (will derive a naive indp)
*)


Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.

Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.


Definition auxarg arg kn (params:context) (t:infolocal -> term) :infolocal -> term :=
  let t1 := arg.(decl_type) in
  let na := arg.(decl_name) in
  fun e =>
    match t1 with
    | tRel i =>
      match is_rec_call e i with
      | Some kk =>
        e <- mktProd (Savelist "args") e na
          (tInd {|inductive_mind := kn;
                  inductive_ind := kk |} []);;
        kptProd NoSave e the_name
          (tApp (geti_info "P" e kk) [get_info_last "args" e (*tRel 0*)])
          t
      | None =>
        kptProd (Savelist "args") e na
          (mapt e t1)
          t
      end
    | tApp (tRel i) tl =>
      match is_rec_call e i with
      | Some kk =>
        e <-
          mktProd (Savelist "args") e na
            (tApp
              (tInd {|inductive_mind := kn;
                      inductive_ind := kk |} [])
            (map (mapt e) tl));;
        kptProd NoSave e the_name
          (tApp
            (geti_info "P" e kk)
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

Definition transformer_result cstrindices constructor_current i_ind :infolocal -> term := fun e =>
  tApp (geti_info "P" e i_ind)
    (
      (map (mapt e) cstrindices)
      ++
      [tApp constructor_current
        (rels_of "params" e ++ rels_of "args" e)]
    ).

Fixpoint Ffix_args kn params args t :=
  match args with
  | [] => t
  | a :: args' => Ffix_args kn params args'(auxarg a kn params t)
  end.

Definition auxctr (i:nat) (ctr:constructor_body) kn params i_ind : infolocal -> term :=
  let the_inductive := {| inductive_mind := kn;
                          inductive_ind := i_ind  |} in
  let constructor_current := tConstruct the_inductive i [] in
  let cstr_type := ctr.(cstr_type) in
  Ffix_args kn params ctr.(cstr_args)
    (transformer_result ctr.(cstr_indices) constructor_current i_ind).

Fixpoint Ffix_ctrs' i kn params i_ind b t : infolocal -> term := fun e =>
  match b with
  | [] => t e
  | a :: b' =>
    mktProd NoSave e the_name
     (auxctr i a kn params i_ind (add_emp_info e (Some "args")))
     (Ffix_ctrs' (S i) kn params i_ind b' t)
  end.

Fixpoint Ffix_bodies_1 i_ind bodies kn t : infolocal ->  term :=
  match bodies with
  | [] => t
  | body :: bodies' => fun e =>
    let the_inductive := {| inductive_mind := kn; inductive_ind := i_ind |} in
    let indices := ind_indices body in
    mktProd (Savelist "P") e prop_name
      (it_mktProd_default (Some "indices") e (indices) $
        fun e'' => tProd the_name
          (tApp (tInd the_inductive [])
            (rels_of "params" e'' ++ rels_of "indices" e''))
          (tSort sProp)
      ) (Ffix_bodies_1 (S i_ind) bodies' kn t) end.

Fixpoint Ffix_bodies_2 i_ind bodies kn params t : infolocal -> term :=
  match bodies with
  | [] => t
  | b :: bodies' =>
    Ffix_ctrs' 0 kn params i_ind (ind_ctors b) (
      Ffix_bodies_2 (S i_ind) bodies' kn params t
    ) end.


(*
  This function generates the term of each type constructor of each inductive body
*)
Definition Ffix_bodies_2' bodies kn params t :=
  Ffix_bodies_2 0 bodies kn params t.


(*
  For an inductive type with n inductive bodies T1, ... Tn

  this function creates the term:
    forall (P1 : ... -> T1 _ -> Prop),
    ...
    forall (Pn : ... -> Tn _ -> Prop),
*)
Definition Ffix_bodies_1' bodies kn t e :=
  Ffix_bodies_1 0 bodies kn t (add_emp_info e (Some "P")).


Definition GenerateIndp (kn : kername) (ty : mutual_inductive_body) : term :=
  let params := ty.(ind_params) in
  let initial_info :=  make_initial_info kn ty in
  let body_main := hd todo ty.(ind_bodies) in
  let the_inductive_main := {| inductive_mind := kn; inductive_ind := 0 |} in
  let indices_main := body_main.(ind_indices) in

  it_kptProd_default (Some "params") initial_info params
    (Ffix_bodies_1' ty.(ind_bodies) kn
      ( e <- Ffix_bodies_2' ty.(ind_bodies) kn params;;
        e <- it_mktProd_default (Some "indices") e (indices_main);;
        e <- mktProd (Saveitem "x") e the_name
              (tApp (tInd the_inductive_main [])
                  (rels_of "params" e ++ rels_of "indices" e)
                );;
        (tApp (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
    ))
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
