Require Import MetaCoq.Programming.

(* From MetaCoq Require Export bytestring. *)
Global Open Scope bs.

Definition the_name := {| binder_name := nNamed "x";
                  binder_relevance := Relevant  |}.

Definition GenerateIdentity_param (na : kername) (ty :  mutual_inductive_body) : term :=

  let params := ty.(ind_params) in
  let n_ind := length ty.(ind_bodies) in
  let initial_info : infolocal :=
    let e := make_initial_info na ty in
    add_info_names e "rels_of_id"
      (map (fun ind_body => {| binder_name := nNamed "id";
                          binder_relevance := Relevant  |}
            ) ty.(ind_bodies))
  in

  let generate_inductive (i:Datatypes.nat) (body: one_inductive_body) :=

    let the_inductive := {| inductive_mind := na; inductive_ind := i |} in
    let indices := body.(ind_indices) in

    let aux : infolocal -> Nat.t -> constructor_body -> (context * (infolocal -> term)) := fun e i b =>
      (b.(cstr_args),
       fun e =>

        let constructor_current := tConstruct the_inductive i Instance.empty in
        tApp
          constructor_current
          ((*the type parameters*) (*X*)
            (rels_of "params" e)
            ++
            (let auxarg arg e:=
              (*current argument*)
              let arg_current := get_arg_current e in
              match arg.(decl_type) with
              (*type with indice/parameter*)
              | tApp (tRel j) tl =>
                match is_rec_call e j with
                | None => arg_current
                | Some kk =>
                  tApp
                    (*recursive call of the identity function*) (*id_vec*)
                    (geti_info "rels_of_id" e kk)
                    ( (*the parameter/indice of the identity function*) (*X n*)
                      (map (mapt e) tl)
                      (*the last argument*) (*v*)
                      ++ [arg_current])
                end
              | tRel j =>
                match is_rec_call e j with
                | None => arg_current
                | Some kk => tApp (geti_info "rels_of_id" e kk) [arg_current]
                end
              | tProd _ _ _ =>
                (***********)
                let fix transformer (t:term) e (u:infolocal -> term) :term :=
                  match t with
                  | tProd na t1 t2 =>
                    kptLambda (Savelist "arglambda") e na
                      (mapt e t1)
                      (fun e => transformer t2 e u)
                  | tApp (tRel j) tl =>
                    match is_rec_call e j with
                    | None => todo (*must be an error*)
                    | Some kk =>
                        tApp (geti_info "rels_of_id" e kk)
                        (map (mapt e) tl ++
                          [tApp (u e) (rels_of "arglambda" e)])
                    end
                  | tRel j =>
                    match is_rec_call e j with
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
                    transformer arg.(decl_type) e (fun e => get_arg_current e)
                end
                (***********)
              | _ => arg_current end
            in
            map_with_infolocal_arg auxarg b.(cstr_args) e)
          )
          )
    in

    {|
      dname := {| binder_name := nNamed "id" ;
                  binder_relevance := Relevant |};
      dtype :=
        e <- it_kptProd_default (Some "params") (initial_info) params;;
        e <- it_mktProd_default (Some "indices") e indices;;
        e <- mktProd NoSave e the_name
              (tApp (tInd the_inductive Instance.empty)
                (rels_of "params" e ++ rels_of "indices" e));;
        tApp (tInd the_inductive Instance.empty)
          (rels_of "params" e ++ rels_of "indices" e);

      (*params is in reverse order*)
      dbody :=
        e <- it_kptLambda_default (Some "params") (initial_info) params;;
        e <- it_mktLambda_default (Some "indices") e (rev indices);;
        e <- mktLambda (Saveitem "x") e the_name
              (tApp (tInd the_inductive Instance.empty)
                (rels_of "params" e ++ rels_of "indices" e));;
        mktCase e
          {|  ci_ind := the_inductive;
              ci_npar := length params;
              ci_relevance := Relevant |}
          (fun _ => [])
          (fun e => rels_of "params" e)
          (fun e => repeat the_name (1 + length indices))
          (fun e =>
            tApp (tInd the_inductive Instance.empty)
            ((rels_of "params" e ) ++ (get_pcontext_indices e)))
          (fun e => rel_of "x" e)
          (fun e => mapi (aux e) body.(ind_ctors));

      rarg := length indices + length params
    |}
  in
  tFix (mapi generate_inductive ty.(ind_bodies)) 0
.


(* Print TemplateMonad. *)
Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

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

(* Load MetaCoqPrelude.

Definition thisfile := $run (tmCurrentModPath tt).
Inductive vec' (X:Type) : nat -> Type:=
  | vnil' : vec' X O
  | vcons' : X -> forall n:nat, vec' X n -> vec' X (S n).

Definition inputf := ($run (tmQuoteInductive (thisfile, "vec'"))).
Compute $Quote vec'_ind. *)
