Require Import MetaCoq.Programming.
Global Open Scope bs.

(*This is an example of using BasePrelude:
  generate the type of induction principle of any inductive type*)


Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.


Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

(*works for inductive type not mutual inductive*)
Definition GenerateIndp (na : kername) (ty :  mutual_inductive_body) : Result term :=
  let params := ty.(ind_params) in
  (*make up the initial information, which has the information of the type name*)
  let initial_info :=  make_initial_info na ty in
  (* suppose single inductive body*)
  (* match hd_error ty.(ind_bodies) with
  | None => Error "0 inductive bodies"
  | Some body => *)
  let body := hd todo ty.(ind_bodies) in
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let indices := body.(ind_indices) in
  (* let (params, no_uniform_params) := SeperateParams na ty in *)

  (*for each constructor cstr in [b], generate a term (ti)*)
  (*returns t1 -> t2 -> ... tk -> [t e_updated]*)
  let aux (b:list constructor_body) (e:infolocal) (t:infolocal -> Result term) : Result term :=

    (* for each type constructor *)
    (* take Vector.t, 'cons : A -> forall n:nat, vec A n -> vec A (S n)' for example *)
    (* ~~~~> forall (a:A) (n:nat) (v:vec A n), P n v -> P (S n) (cons a n v) *)
    let auxctr (i:nat) (ctr:constructor_body) (e:infolocal) : Result term :=
      let constructor_current := tConstruct the_inductive i [] in
      let cstr_type := ctr.(cstr_type) in
      (** trick **) let e := add_emp_info "args" e in

      (*transforme the return type of constructor*)
      (*'cons : ... -> vec A (S n)'   ~~~>   P (S n) (cons A a n v)
                        ^^^^^^^^^^                                *)
      let transformer_result :infolocal -> Result term := fun e =>
        tApp' (rel_of "P" e)
          (
            (map (mapt e) ctr.(cstr_indices))
            ++
            [tApp' (Ok constructor_current)
              (rels_of "params" e ++ rels_of "args" e)]
          )
      in

      (*transforme the argument*)
        (*A ~~~> forall (a:A) -> [t] *)
        (*forall (n:nat) ~~~> forall (n:nat) -> [t]*)
        (*vec A n ~~~> forall (v:vec A n) -> P n v -> [t] *)
      let auxarg arg (t:infolocal -> Result term) :infolocal -> Result term :=
        let t1 := arg.(decl_type) in
        let na := arg.(decl_name) in
        fun e =>
        match t1 with
        | tRel i =>
          match is_rec_call e i with
          | Ok (Some _) =>
            e <- mktProd (Savelist "args") e na (mapt e t1);;
            kptProd NoSave e the_name
              (tApp' (rel_of "P" e) [get_info_last "args" e (*tRel 0*)])
              t
          (*ex. forall (n:nat)/  A*)
          | Ok None =>
            (*save the argument n into information list "args"*)
            kptProd (Savelist "args") e na
              (mapt e t1)
              t
          | Error msg => Error msg
          end
        (*ex. vec A n*)
        | tApp (tRel i) tl =>
          match is_rec_call e i with
          | Ok (Some _) =>
            (*save the argument v into information list "args"*)
            e <-
              mktProd (Savelist "args") e na
                (*type of v: vec A n*)
                (mapt e t1);;
            (* P n v -> [t]*)
            kptProd NoSave e the_name
              (tApp'
                (rel_of "P" e)
                (let tl := n_tl tl (length params) in
                  (map (mapt e) tl) (*n*) ++ [get_info_last "args" e (*tRel 0*)] (*v*))
              ) t
          | Ok None =>
            kptProd (Savelist "args") e na
              (mapt e t1)
              t
          | Error msg => Error msg
          end
        (**********************)
        | tProd na _ _ =>
          match check_return_type t1 e with
          | Error msg => Error msg
          | Ok None => kptProd (Savelist "args") e na (mapt e t1) t
          | Ok (Some _) =>
            let fix aux_nested e (t1:term) : Result term :=
              match t1 with
              | tProd na ta tb =>
                kptProd (Savelist "arglambda") e na
                  (mapt e ta) (fun e => aux_nested e tb)
              | tRel i =>
                match is_rec_call e i with
                | Error msg => Error msg
                | Ok None => Error "?0"
                | Ok (Some _) =>
                  tApp' (rel_of "P" e)
                    [tApp' (get_info_last "args" e) (rels_of "arglambda" e)]
                end
              | tApp (tRel i) tl =>
                match is_rec_call e i with
                | Error msg => Error msg
                | Ok None => Error "?1"
                | Ok (Some _) =>
                  tApp' (rel_of "P" e)
                    (let tl := n_tl tl (length params) in
                      (map (mapt e) tl) ++
                      [tApp' (get_info_last "args" e) (rels_of "arglambda" e)])
                end
              | _ => Error "todo"
              end in
            e <- mktProd (Savelist "args") e na (mapt e t1);;
            kptProd NoSave e the_name (aux_nested e t1) t
          end
        (**********************)
        | _ => kptProd (Savelist "args") e na
                (mapt e t1)
                t
        end
      in
      fold_left_ie (fun _ => auxarg) ctr.(cstr_args) (transformer_result) e
    in
    fold_right_ie
      (fun i a t e => mktProd NoSave e the_name (auxctr i a e) t)
      b t e
  in

  (*
    for type
    Inductive T (A1:Param1) ... (Ak:Paramk) : Ind1 -> ... -> Indm -> Type.

    Its inductive principle has type:
    (not uniform parameter works the same way as index, omit the explication below)

    forall (A1:Param1) ... (Ak:Paramk),
    forall (P: forall (i1:Ind1) ... (im:Indm), T A1 ... Ak i1 ... im -> Prop),
      ...(generated according to the constructors)
    -> forall (i1:Ind1) ... (im:Indm),
        forall (x:T A1 ... Ak i1 ... im), P i1 ... im x
  *)

  (* ATTENTION: in the quotation of inductive type, the parameters, indices are in reverse order *)
  (*forall (A1:Param1) ... (Ak:Paramk),*)

  e <- it_kptProd_default (Some "params") initial_info params;;
  (*forall P:?, ?*)
  e <- mktProd (Saveitem "P") e prop_name
        (*type of P: forall (i1:Ind1) ... (im:Indm), T A1 ... Ak i1 ... im -> Prop*)
        ((*forall (i1:Ind1) ... (im:Indm)*)
          e <- it_mktProd_default (Some "indices") e indices;;
          tProd' the_name
            (*T A1 ... Ak i1 ... im*)
            (tApp' (Ok $ tInd the_inductive [])
              (rels_of "params" e ++ rels_of "indices" e)
            )
            (Ok $ tSort sProp) (*Prop*)
        );;
  (*see details in the [aux] above*)
  e <- aux body.(ind_ctors) e;;
    (*forall (i1:Ind1) ... (im:Indm),
      forall (x:T A1 ... Ak i1 ... im), P i1 ... im x*)
    e <- it_mktProd_default (Some "indices") e (indices);;
    e <- mktProd (Saveitem "x") e the_name
          (*type of x: T A1 ... Ak i1 ... im*)
          (tApp' (Ok $ tInd the_inductive [])
              (rels_of "params" e ++ rels_of "indices" e)
            );;
    (*P i1 ... im x*)
    (tApp' (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
  .


(****************************************************************)
(*for mutual inductive type*)
(* Axiom print_context: forall {A}, infolocal -> A. *)

Definition GenerateIndp_mutual' (kername : kername) (ty :  mutual_inductive_body) (n:nat): Result term :=
  let params := ty.(ind_params) in
  let initial_info := make_initial_info kername ty in
  let bodies := ty.(ind_bodies) in
  let n_ind := length ty.(ind_bodies) in
  let (params, no_uniform_params) := SeperateParams kername ty in

  let aux (e:infolocal) (b:list constructor_body) (j:nat) (t:infolocal -> Result term) :Result term :=
    let auxctr (i:nat) (ctr:constructor_body) (e:infolocal): Result term :=
      let constructor_current :=
        tConstruct {| inductive_mind := kername; inductive_ind := j |} i [] in
      (** trick **) let e := add_emp_info "args" e in
      let transformer_result :infolocal -> Result term := fun e =>
        tApp' (geti_info "P" e j)
          (
            rels_of "no_uniform_params" e
            ++
            (map (mapt e) ctr.(cstr_indices))
            ++
            [tApp' (Ok constructor_current)
              (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "args" e)]
          )
      in
      let auxarg arg (t:infolocal-> Result term) :infolocal -> Result term := fun e =>
        let t1 := arg.(decl_type) in
        let na := arg.(decl_name) in
        match arg.(decl_body) with
        | Some t0 => kptLetIn NoSave e t0 na (mapt e t0) (mapt e t1) t
        | None =>
          match normal e t1 with
          | None => Error "term not normalisable"
          | Some t1 =>
            match t1 with
            | tRel i =>
              match is_rec_call e i with
              | Ok (Some kk) =>
                e <- mktProd (Savelist "args") e na (mapt e t1);;
                kptProd NoSave e the_name
                  (
                    tApp' (geti_info "P" e kk) [get_info_last "args" e])
                  ( t)
              | Ok None =>
                kptProd (Savelist "args") e na
                  (mapt e t1)
                  ( t)
              | Error msg => Error msg
              end
            | tApp (tRel i) tl =>
              match is_rec_call e i with
              | Ok (Some kk) =>
                e <- mktProd (Savelist "args") e na (mapt e t1);;
                kptProd NoSave e the_name
                  (tApp'
                    (geti_info "P" e kk)
                    (let tl := n_tl tl (length params) in
                      (map (mapt e) tl) ++ [(get_info_last "args" e)])
                  ) ( t)
              | Ok None =>
                kptProd (Savelist "args") e na
                  (mapt e t1)
                  ( t)
              | Error msg => Error msg
              end
            (*****************************************)
            | tProd na _ _ =>
              match check_return_type t1 e with
              | Ok None => kptProd (Savelist "args") e na ( mapt e t1) ( t)
              | Ok (Some _) =>
                let fix aux_nested e t1 :=
                  match t1 with
                  | tProd na ta tb =>
                    kptProd (Savelist "arglambda") e na
                      (mapt e ta) (fun e => aux_nested e tb)
                  | tRel i =>
                    match is_rec_call e i with
                    | Ok None => Error "?"
                    | Ok (Some kk) =>
                      tApp' (geti_info "P" e kk)
                        [tApp' (get_info_last "args" e) (rels_of "arglambda" e)]
                    | Error msg => Error msg
                    end
                  | tApp (tRel i) tl =>
                    match is_rec_call e i with
                    | Ok None => Error "?"
                    | Ok (Some kk) =>
                      tApp' (geti_info "P" e kk)
                        (let tl := n_tl tl (length params) in
                          (map (mapt e) tl) ++
                          [tApp' (get_info_last "args" e) (rels_of "arglambda" e)])
                    | Error msg => Error msg
                    end
                  | _ => Error "todo" end in
                e <- mktProd (Savelist "args") e na (mapt e t1);;
                kptProd NoSave e the_name (aux_nested e t1) ( t)
              | Error msg => Error msg
              end
            (*****************************************)
            | _ => kptProd (Savelist "args") e na
                    (mapt e t1)
                    ( t)
            end
          end
        end
      in
      fold_left_ie (fun _ => auxarg) ctr.(cstr_args) (transformer_result) e
    in
    fold_right_ie
      (fun i a t e =>
        mktProd NoSave e the_name
          (it_kptProd_default (Some "no_uniform_params") e (no_uniform_params) $
            auxctr i a) t
      ) b t e
  in
  let mainbody := nth n bodies todo in
  let indices_main := mainbody.(ind_indices) in
  let the_inductive_main := {| inductive_mind := kername; inductive_ind := 0|} in

  it_kptProd_default (Some "params") initial_info params $
    fold_right_ie (
      fun i body t e =>
        let the_inductive := {| inductive_mind := kername; inductive_ind :=i |} in
        let indices := body.(ind_indices) in
        mktProd (Savelist "P") e prop_name
          (
          e <- it_kptProd_default (Some "no_uniform_params") e (no_uniform_params);;
          e <- it_mktProd_default (Some "indices") e (indices);;
          tProd' the_name
            (tApp' (Ok $ tInd the_inductive [])
              (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e))
            (Ok $ tSort sProp)
          ) t
    ) bodies
      (fold_right_ie
        (fun i body t e => aux e body.(ind_ctors) i t)
        bodies
        (fun e =>
          e <- it_kptProd_default (Some "no_uniform_params") e (no_uniform_params);;
          e <- it_mktProd_default (Some "indices") e (indices_main);;
          e <- mktProd (Saveitem "x") e the_name
                (tApp' (Ok $ tInd the_inductive_main [])
                  (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e));;
          tApp' (geti_info "P" e 0)
              (rels_of "no_uniform_params" e ++ rels_of "indices" e ++ [rel_of "x" e]))
      )
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
      match id with
      | Ok id =>
        $let u := tmUnquote id in
        $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
          match out with
          | Some name => tmDefinitionRed name (Some hnf) r ;; tmPrint r ;; ret tt
          | None => tmPrint r
          end
      | Error msg =>
        $let r := tmEval all msg in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; tmPrint r ;; ret tt
        | None => tmPrint r
        end
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


