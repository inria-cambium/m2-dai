Require Import MetaCoq.Programming.
Global Open Scope bs.

(* Definition fold_prod
  (aux1: term -> (infolocal -> term) -> infolocal -> term)
  (aux2: term -> infolocal -> term)
  (t:term) (e:infolocal): term :=
  let fix Ffix t e :=
    match t with
    | tProd na t1 t2 =>
      aux1 t1 (fun e => Ffix t2 (next na None e)) e
    | _ => aux2 t e
    end in
  Ffix t e. *)

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.


Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

Axiom print_context: forall {A}, infolocal -> A.

Definition GenerateIndp_mutual' (kername : kername) (ty :  mutual_inductive_body) (n:nat): term :=
  let params := ty.(ind_params) in
  let initial_info := make_initial_info kername ty in
  let bodies := ty.(ind_bodies) in
  let n_ind := length ty.(ind_bodies) in
  let (params, no_uniform_params) := SeperateParams kername ty in

  let auxparam := (fun decl t0 e =>
    match decl_body decl with
    | None => mktProd (Savelist "params") e (decl_name decl) (mapt e (decl_type decl)) t0
    | Some body => mktLetIn NoSave e decl.(decl_name)
                      (mapt e body) (mapt e decl.(decl_type)) t0 end
    )
  in

  let auxparam_nu := (fun decl t0 e =>
    match decl_body decl with
    | None => mktProd (Savelist "no_uniform_params") e (decl_name decl) (mapt e (decl_type decl)) t0
    | Some body => mktLetIn NoSave e decl.(decl_name)
                      (mapt e body) (mapt e decl.(decl_type)) t0 end
    )
  in

  let auxindice := (fun decl t0 e =>
      match decl_body decl with
      | None => mktProd (Savelist "indices") e (decl_name decl) (mapt e (decl_type decl)) t0
      | Some body => mktLetIn NoSave e decl.(decl_name)
                        (mapt e body) (mapt e decl.(decl_type)) t0 end
    )
  in

  let aux (e:infolocal) (b:list constructor_body) (j:nat) (t:infolocal -> term) :term :=
    let auxctr (i:nat) (ctr:constructor_body) (e:infolocal): term :=
      let constructor_current :=
        tConstruct {| inductive_mind := kername; inductive_ind := j |} i [] in
      let transformer_result :infolocal -> term := fun e =>
        tApp (geti_info "P" e j)
          (
            rels_of "no_uniform_params" e
            ++
            (map (mapt e) ctr.(cstr_indices))
            ++
            [tApp constructor_current
              (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "args" e)]
          )
      in
      let auxarg arg (t:infolocal->term) :infolocal -> term := fun e =>
        let t1 := arg.(decl_type) in
        let na := arg.(decl_name) in
        match arg.(decl_body) with
        | Some t0 => mktLetIn NoSave e na (mapt e t0) (mapt e t1) t
        | None =>
          match normal e t1 with
          | None => print_context e
          | Some t1 =>
            match t1 with
            | tRel i =>
              match is_rec_call e i with
              | Some kk =>
                mktProd (Savelist "args") e na
                  (
                    (tInd
                      {| inductive_mind := kername; inductive_ind := kk |}
                      [])
                  )
                  (fun e =>
                    mktProd NoSave e the_name
                      (
                        tApp (geti_info "P" e kk) (*tRel 0*)[get_info_last "args" e])
                      t)
              | None =>
                mktProd (Savelist "args") e na
                  (mapt e t1)
                  t
              end
            | tApp (tRel i) tl =>
              match is_rec_call e i with
              | Some kk =>
                mktProd (Savelist "args") e na
                  (
                    tApp
                      (tInd
                        {| inductive_mind := kername; inductive_ind := kk |}
                        [])
                      (map (mapt e) tl))
                  (fun e =>
                    mktProd NoSave e the_name
                      (tApp
                        (geti_info "P" e kk)
                        (let tl := n_tl tl (length params) in
                          (map (mapt e) tl) ++ [(get_info_last "args" e)])
                      ) t)
              | None =>
                mktProd (Savelist "args") e na
                  (mapt e t1)
                  t
              end
            (*****************************************)
            | tProd na _ _ =>
              match check_return_type t1 e with
              | None => mktProd (Savelist "args") e na ( mapt e t1) t
              | Some _ =>
                let fix aux_nested e t1 :=
                  match t1 with
                  | tProd na ta tb =>
                    kptProd (Savelist "arglambda") e na
                      (mapt e ta) (fun e => aux_nested e tb)
                  | tRel i =>
                    match is_rec_call e i with
                    | None => todo
                    | Some kk =>
                      tApp (geti_info "P" e kk)
                        [tApp (get_info_last "args" e) (rels_of "arglambda" e)]
                    end
                  | tApp (tRel i) tl =>
                    match is_rec_call e i with
                    | None => todo
                    | Some kk =>
                      tApp (geti_info "P" e kk)
                        (let tl := n_tl tl (length params) in
                          (map (mapt e) tl) ++
                          [tApp (get_info_last "args" e) (rels_of "arglambda" e)])
                    end
                  | _ => todo end in
                (* let aux_nested e t1 :=
                  fold_prod (
                    fun t t0 e =>
                      mktProd (Savelist "arglambda") e the_name
                        (mapt e t) t0
                  )
                  (fun t e =>
                    match t with
                    | tRel i =>
                      match is_rec_call e i with
                      | None => todo
                      | Some kk =>
                        tApp (geti_info "P" e kk)
                          [tApp (get_info_last "args" e) (rels_of "arglambda" e)]
                      end
                    | tApp (tRel i) tl =>
                      match is_rec_call e i with
                      | None => todo
                      | Some kk =>
                        tApp (geti_info "P" e kk)
                          (let tl := n_tl tl (length params) in
                            (map (mapt e) tl) ++
                            [tApp (get_info_last "args" e) (rels_of "arglambda" e)])
                      end
                    | _ => todo end
                  ) t1 e in *)
                e <- mktProd (Savelist "args") e na (mapt e t1);;
                mktProd NoSave e the_name (aux_nested e t1) t
              end
            (*****************************************)
            | _ => mktProd (Savelist "args") e na
                    (mapt e t1)
                    t
            end
          end
        end
      in
      fold_args auxarg ctr.(cstr_args) (transformer_result) e
    in
    fold_ctrs
      (fun i a t e =>
        mktProd NoSave e the_name
          (fold_params auxparam_nu (no_uniform_params)
            (auxctr i a) e)
        t
      ) b t e
  in
  let mainbody := nth n bodies todo in
  let indices_main := mainbody.(ind_indices) in
  let the_inductive_main := {| inductive_mind := kername; inductive_ind := 0|} in

  initial_info |>
  fold_params auxparam params $
    fold_bodies (
      fun i body t e =>
        let the_inductive := {| inductive_mind := kername; inductive_ind :=i |} in
        let indices := body.(ind_indices) in
        mktProd (Savelist "P") e prop_name
          (fold_params auxparam_nu no_uniform_params
          (fold_indices auxindice indices
            (fun e =>
            tProd the_name
                (tApp (tInd the_inductive [])
                  (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e))
                (tSort sProp)
            ) ) e) t
    ) bodies
      (fold_bodies
        (fun i body t e =>
          aux e body.(ind_ctors) i t)
        bodies
        (
          fold_params auxparam_nu no_uniform_params $
          e <- fold_indices auxindice indices_main ;;
          e <- mktProd (Saveitem "x") e the_name
                (tApp (tInd the_inductive_main [])
                  (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e)) ;;
          tApp (geti_info "P" e 0)
              (rels_of "no_uniform_params" e ++ rels_of "indices" e ++ [rel_of "x" e])
      ))
  .

Definition GenerateIndp_mutual kn ty := GenerateIndp_mutual' kn ty 0.

Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

Definition generate_indp {A} (a : A) (out : option ident): TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
      let kn := ind.(inductive_mind) in
      $let mind := tmQuoteInductive kn in
      let id := GenerateIndp_mutual kn mind in
      $let u := tmUnquote id in
      $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; tmPrint r ;; ret tt
        | None => tmPrint r
        end
    | _ => tmFail "no inductive"
    end.

Notation "'Derive' 'InductivePrinciple' a 'as' id" := (generate_indp a (Some id)) (at level 0).

Definition print_indp {A} (a : A) : TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
        let kn := ind.(inductive_mind) in
        $let mind := tmQuoteInductive kn in
          let id := GenerateIndp_mutual kn mind in
          tmEval cbv id >>= tmPrint
    | _ => tmFail "no inductive"
    end.

Notation "'PrintInductivePrinciple' a" := (print_indp a) (at level 0).
