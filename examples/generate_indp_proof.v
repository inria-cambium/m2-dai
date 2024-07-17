Require Import MetaCoq.Programming.
Require Import generate_inductive_principle.

(* From MetaCoq Require Export bytestring. *)
Global Open Scope bs.

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.
Definition fix_name :=  {| binder_name := nNamed "F"; binder_relevance := Relevant |}.

(* Print redo. *)

Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.


Axiom print_context: forall {A}, context -> A.


(* Search (nat -> string). *)
(* Print tFix. *)

(* Print rev_app. *)


Definition GenerateIndp_proof (kername : kername) (ty :  mutual_inductive_body) : term :=

  let params := ty.(ind_params) in
  let n_ind := length ty.(ind_bodies) in
  let initial_info : infolocal :=
    let e := make_initial_info kername ty in
    e
  in


  let aux (e:infolocal) (b:list constructor_body) (j:nat) (t:infolocal -> term) :term :=
    let auxctr (i:nat) (ctr:constructor_body) (e:infolocal): term :=
      let constructor_current :=
        tConstruct {| inductive_mind := kername; inductive_ind := j |} i [] in
      let transformer_result :infolocal -> term := fun e =>
        tApp (geti_info "P" e j)
          (
            (map (mapt e) ctr.(cstr_indices))
            ++
            [tApp constructor_current
              (rels_of "params" e ++ rels_of "args" e)]
          )
      in
      let auxarg arg (t:infolocal->term) :infolocal -> term := fun e =>
        let t1 := arg.(decl_type) in
        let na := arg.(decl_name) in
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
                kptProd NoSave e the_name
                  (
                    tApp (geti_info "P" e kk) (*tRel 0*)[get_info_last "args" e])
                  t)
          | None =>
            kptProd (Savelist "args") e na
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
                kptProd NoSave e the_name
                  (tApp
                    (geti_info "P" e kk)
                    (let tl := n_tl tl (length params) in
                      (map (mapt e) tl) ++ [(get_info_last "args" e)])
                  ) t)
          | None =>
            kptProd (Savelist "args") e na
              (mapt e t1)
              t
          end
        (*****************************************)
        | tProd na _ _ =>
          match check_return_type t1 e with
          | None => kptProd (Savelist "args") e na ( mapt e t1) t
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
            mktProd (Savelist "args") e na (mapt e t1)
              (fun e => kptProd NoSave e the_name (aux_nested e t1) t)
          end
        (*****************************************)
        | _ => kptProd (Savelist "args") e na
                (mapt e t1)
                t
        end
      in
      fold_left_ie (fun _ => auxarg) ctr.(cstr_args) (transformer_result) e
    in
    fold_right_ie
      (fun i a t e =>
        mktLambda (Savelist (String.append "Pctr" (string_of_nat j) )) e the_name
          (auxctr i a e) t
      ) b t e
  in

  let aux' : infolocal -> Nat.t -> Nat.t -> constructor_body -> (context * (infolocal -> term)) :=
    fun e j i b =>
    (b.(cstr_args), fun e =>
      tApp (geti_info (String.append "Pctr" (string_of_nat j)) e i)
        (fold_left
          (fun a b => app b a)
              (let auxarg arg e :=
                let arg_current := get_arg_current e in
                match arg.(decl_type) with
                | tApp (tRel j) tl =>
                  match is_rec_call e j with
                  | None => [arg_current]
                  | Some kk =>
                    [arg_current;
                    tApp
                      (geti_info "F" e kk)
                        ((map (mapt e) (n_tl tl (length params)) )
                          ++ [arg_current])]
                  end
                | tRel j =>
                  match is_rec_call e j with
                  | None => [arg_current]
                  | Some kk =>
                    [ arg_current;
                      tApp (geti_info "F" e kk) [arg_current]]
                  end
                | tProd _ _ _ => todo
                | _ => [arg_current] end
              in
              map_with_infolocal_arg auxarg b.(cstr_args) e)
              []
        )
    )
  in
  let bodies := ty.(ind_bodies) in

  let generate_fix e j mainbody : def term :=
    let indices_main := mainbody.(ind_indices) in
    let the_inductive_main := {| inductive_mind := kername; inductive_ind := j|} in

    mktfixpoint (Savelist "F") (map (fun _ => fix_name) bodies) e
      fix_name
      ( e <- it_mktProd_default (Some "indices") e indices_main;;
        e <- mktProd (Saveitem "x") e the_name
              (tApp (tInd the_inductive_main [])
                (rels_of "params" e ++ rels_of "indices" e));;
        tApp (geti_info "P" e j)
            (rels_of "indices" e ++ [rel_of "x" e])
            )
      (fun e =>
        e <- it_mktLambda_default (Some "indices") e (indices_main);;
        e <- mktLambda (Saveitem "x") e the_name
              (tApp (tInd the_inductive_main [])
                (rels_of "params" e ++ rels_of "indices" e));;
        (mktCase e
          {|  ci_ind := the_inductive_main;
              ci_npar := length params;
              ci_relevance := Relevant |}
          (fun _ => [])
          (fun e => rels_of "params" e)
          (fun e => repeat the_name (1 + length indices_main))
          (fun e => tApp (geti_info "P" e j) (get_pcontext e))
          (fun e => rel_of "x" e)
          (fun e => mapi (aux' e j) mainbody.(ind_ctors)))
      )
      (length indices_main)
  in

  it_kptLambda_default (Some "params") initial_info params $
  fold_right_ie (
    fun i body t e =>
      let the_inductive := {| inductive_mind := kername; inductive_ind :=i |} in
      let indices := body.(ind_indices) in
      mktLambda (Savelist "P") e prop_name
        (
        e <- it_mktProd_default (Some "indices") e (indices);;
        tProd the_name
          (tApp (tInd the_inductive [])
            (rels_of "params" e ++ rels_of "indices" e))
          (tSort sProp)
        ) t
  ) bodies
    (fold_right_ie
      (fun i body t e => aux e body.(ind_ctors) i t)
      bodies
      (fun e =>
        tFix (mapi (fun i body => generate_fix e i body) ty.(ind_bodies)) 0))
  .


Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

Definition generate_indp {A} (a : A) (out : option ident): TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
      let kn := ind.(inductive_mind) in
      $let mind := tmQuoteInductive kn in
      let id := GenerateIndp_proof kn mind in
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
          let id := GenerateIndp_proof kn mind in
          tmEval cbv id >>= tmPrint
    | _ => tmFail "no inductive"
    end.

Notation "'PrintInductivePrinciple' a" := (print_indp a) (at level 0).
