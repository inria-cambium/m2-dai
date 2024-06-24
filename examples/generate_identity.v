Require Import MetaCoq.Programming.BasePrelude.

(* From MetaCoq Require Export bytestring. *)
Global Open Scope bs.

Definition the_name := {| binder_name := nNamed "x";
                  binder_relevance := Relevant  |}.

Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).


Notation " x '<-' c1 ';;' c2" := ( c1 (fun x => c2))
                                     (at level 100, c1 at next level, right associativity) : monad_scope.

Definition GenerateIdentity_param (na : kername) (ty :  mutual_inductive_body) : term :=

  let params := ty.(ind_params) in
  let n_ind := length ty.(ind_bodies) in
  let initial_info : extrainfo :=
    let e := make_initial_info na ty in
    add_info_names e "rels_of_id"
      (map (fun ind_body => {| binder_name := nNamed "id";
                          binder_relevance := Relevant  |}
            ) ty.(ind_bodies))
  in

  let generate_inductive (i:Datatypes.nat) (body: one_inductive_body) :=

    let the_inductive := {| inductive_mind := na; inductive_ind := i |} in
    let indices := body.(ind_indices) in

    let aux : extrainfo -> Nat.t -> constructor_body -> (context * (extrainfo -> term)) := fun e i b =>
      (b.(cstr_args),
       fun e =>

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
                      (geti_info "rels_of_id" e kk)
                      ( (*the parameter/indice of the identity function*) (*X n*)
                        (map (type_rename_transformer e) tl)
                        (*the last argument*) (*v*)
                        ++ [arg_current])
                  end
                | tRel j =>
                  match is_recursive_call_gen e j with
                  | None => arg_current
                  | Some kk => tApp (geti_info "rels_of_id" e kk) [arg_current]
                  end
                | tProd _ _ _ =>
                  (***********)
                  let fix transformer (t:term) e (u:extrainfo -> term) :term :=
                    match t with
                    | tProd na t1 t2 =>
                      kptLambda (Savelist "arglambda") na e
                        (type_rename_transformer e t1)
                        (fun e => transformer t2 e u)
                    | tApp (tRel j) tl =>
                      match is_recursive_call_gen e j with
                      | None => todo (*must be an error*)
                      | Some kk =>
                          tApp (geti_info "rels_of_id" e kk)
                          (map (type_rename_transformer e) tl ++
                            [tApp (u e) (rels_of "arglambda" e)])
                      end
                    | tRel j =>
                      match is_recursive_call_gen e j with
                      | None => todo (*must be an error*)
                      | Some kk =>
                          tApp (geti_info "rels_of_id" e kk) [tApp (u e) (rels_of "arglambda" e)]
                      end
                    | _ => todo
                    end
                  in
                  match check_return_type arg.(decl_type) e with
                  | None => arg_current
                  | Some _ =>
                      transformer arg.(decl_type) e (fun e => rel_of "arg_current" e)
                  end
                  (***********)
                | _ => arg_current end
              in
              map_with_extrainfo_arg auxarg b.(cstr_args) e)
            )
          )
          )
    in

    {|
      dname := {| binder_name := nNamed "id" ;
                  binder_relevance := Relevant |};
      dtype :=
        e <- it_kptProd (Some "params") (params) (initial_info);;
        e <- it_mktProd (Some "indices") (indices) e ;;
        e <- mktProd NoSave the_name e
              (tApp (tInd the_inductive Instance.empty)
                (rels_of "params" e ++ rels_of "indices" e));;
        tApp (tInd the_inductive Instance.empty)
          (rels_of "params" e ++ rels_of "indices" e);

      (*params is in reverse order*)
      dbody :=
        e <- it_kptLambda (Some "params") (params) (initial_info);;
        e <- it_mktLambda (Some "indices") (rev indices) e;;
        e <- mktLambda (Saveitem "x") the_name e
              (tApp (tInd the_inductive Instance.empty)
                (rels_of "params" e ++ rels_of "indices" e));;
        fancy_tCase e
          (fun _ => the_inductive)
          (fun _ => Relevant)
          (fun _ => [])
          (fun e => rels_of "params" e)
          (fun e => repeat the_name (1 + length (lookup_list e.(info) "indices")))
          (fun e =>
            tApp (tInd the_inductive Instance.empty)
            ((rels_of "params" e ) ++ (rels_of "pcontext_indices" e)))
          (fun e => rel_of "x" e)
          (fun e => mapi (aux e) body.(ind_ctors));

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
