Require Import BasePrelude.
Require Import param_checker.
Global Open Scope bs.

(*This is an example of using BasePrelude:
  generate the type of inductive principle of any inductive type*)

Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.


Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

(*seperating the list of parameters into "uniform params" and "non-uniform params"*)
(*for inductive principle, "non-uniform parameter" is treated the same way as index (different from uniform)*)
(*the function below just find the first non-uniform param and split the list,
  the params after the first non-uniform one are regarded as if they are not uniform        *)
Definition SeperateParams (kn:kername) (ty:mutual_inductive_body) :=
  let findi {X} (f: X -> bool) (l:list X) :option nat :=
    let fix Ffix l n:=
      match l with
      | [] => None
      | y :: l' => if f y then Some n else Ffix l' (n+1)
      end
    in
    Ffix l 0 in
  let params := ty.(ind_params) in
  let bl := CheckUniformParam kn ty in
  match findi (fun b => negb b) bl with
  | None => (params, [])
  | Some i => (skipn (length params - i) params, firstn (length params - i) params)
  end.

(* Definition SeperateParams2 (kn:kername) (ty:mutual_inductive_body) :=
  let params := ty.(ind_params) in
  let bl := CheckUniformParam kn ty in
  let fix Ffix l1 l2 (bl:list bool) :=
    match bl with
    | [] => (l1, l2)
    | b :: bl => if b then Ffix (b :: l1) l2 bl else Ffix l1 (b :: l2) bl
    end
  in
  Ffix [] [] (rev bl). *)

(*works for inductive type not mutual inductive*)
Definition GenerateIndp (na : kername) (ty :  mutual_inductive_body) : term :=
    let params := ty.(ind_params) in
    (*make up the initial information, which has the information of the type name*)
    let initial_info :=  make_initial_info na ty in
    (* suppose single inductive body*)
    let body := hd todo ty.(ind_bodies) in
    let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
    let indices := body.(ind_indices) in
    (* let (params, no_uniform_params) := SeperateParams na ty in *)

    (*for each constructor cstr in [b], generate a term (ti)*)
    (*returns t1 -> t2 -> ... tk -> [t e_updated]*)
    let aux (e:extrainfo) (b:list constructor_body) (t:extrainfo -> term) :term :=
      let fix Ffix e b (t:extrainfo -> term) i :=

        (* for each type constructor *)
        (* take Vector.t, 'cons : A -> forall n:nat, vec A n -> vec A (S n)' for example *)
        (* ~~~~> forall (a:A) (n:nat) (v:vec A n), P n v -> P (S n) (cons a n v) *)
        let auxctr (e:extrainfo) (ctr:constructor_body) i : term :=
          let constructor_current := tConstruct the_inductive i [] in
          let cstr_type := ctr.(cstr_type) in
          (*get the return type of the type constructor*)
          (*vec A (S n)*)
          let return_type: term :=
            (fix Ffix t :=
              match t with
              | tProd _ _ t => Ffix t
              | _ => t
              end ) cstr_type
          in
          (*transforme the return type of constructor*)
          (*'cons : ... -> vec A (S n)'   ~~~>   P (S n) (cons A a n v)
                            ^^^^^^^^^^                                *)
          let transformer_result (t:term) :extrainfo -> term := fun e =>
            match t with
            | tApp (tRel i) tl =>
              (*check that the return type of the constructor is exactly the type which we are defining*) (*vec*)
              match is_recursive_call_gen e i with
              | Some _ =>
                  tApp
                  (rel_of "P" e)
                  (*tl ~~ [A; S n]*)
                  (let tl := n_tl tl (length params) in
                    (*get rid of the parameter [A], remind that P has type (forall (n:nat), vec A n -> Prop)*)
                    (map (type_rename_transformer e) tl) (*renaming transformation*) (*S n ~~~~> S (tRel _)*)
                      ++
                      [           (*cons*)
                        tApp constructor_current
                          (* A *)                                                    (*  a n v  *)
                          (rels_of "params" e ++ rels_of "args" e)
                      ])
              | None => todo (*must be an error*)
              end
            | tRel i => (*for other inductive type, not parametric, without indices*)
              match is_recursive_call_gen e i with
              | Some _ =>
                tApp
                  (rel_of "P" e)
                  [ tApp constructor_current
                    (rels_of "params" e ++ rels_of "args" e)
                    ]
              | None => todo (*must be an error*)
              end
            | _ => todo end (*must be an error*)
          in
          (*transforme the argument*)
            (*A ~~~> forall (a:A) -> [t] *)
            (*forall (n:nat) ~~~> forall (n:nat) -> [t]*)
            (*vec A n ~~~> forall (v:vec A n) -> P n v -> [t] *)
          let auxarg arg (t:extrainfo -> term) :extrainfo -> term :=
            let t1 := arg.(decl_type) in
            let na := arg.(decl_name) in
            fun e =>
            match t1 with
            | tRel i =>
              match is_recursive_call_gen e i with
              | Some _ =>
                mktProd (Savelist "args") na e
                  (fun e => tInd the_inductive [])
                  (fun e =>
                    kptProd NoSave the_name e
                      (fun e => tApp (rel_of "P" e) [geti_info "args" e 0 (*tRel 0*)])
                      t)
              (*ex. forall (n:nat)/  A*)
              | None =>
                (*save the argument n into information list "args"*)
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1) (*renaming transformation*)
                  t
              end
            (*ex. vec A n*)
            | tApp (tRel i) tl =>
              match is_recursive_call_gen e i with
              | Some _ =>
               (*save the argument v into information list "args"*)
               (*forall v:?, ?*)
                mktProd (Savelist "args") na e
                  (*type of v: vec A n*)
                  (fun e =>
                    tApp (tInd the_inductive []) (map (type_rename_transformer e) tl))
                  (* P n v -> [t]*)
                  (fun e =>
                    kptProd NoSave the_name e
                      (fun e => tApp
                        (rel_of "P" e)
                        (let tl := n_tl tl (length params) in
                          (map (type_rename_transformer e) tl) (*n*) ++ [geti_info "args" e 0 (*tRel 0*)] (*v*))
                      ) t)
              | None =>
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1)
                  t
              end
            (**********************)
            | tProd na _ _ =>
              match check_return_type t1 e with
              | None => kptProd (Savelist "args") na e (fun e => type_rename_transformer e t1) t
              | Some _ =>
                let fix aux_nested e t1 :=
                  match t1 with
                  | tProd na ta tb =>
                    kptProd (Savelist "arglambda") na e
                      (fun e => type_rename_transformer e ta) (fun e => aux_nested e tb)
                  | tRel _ =>
                    match is_recursive_call_gen e i with
                    | None => todo
                    | Some kk =>
                      tApp (rel_of "P" e)
                        [tApp (geti_info "args" e 0) (rels_of "arglambda" e)]
                    end
                  | tApp (tRel _) tl =>
                    match is_recursive_call_gen e i with
                    | None => todo
                    | Some kk =>
                      tApp (rel_of "P" e)
                        (let tl := n_tl tl (length params) in
                          (map (type_rename_transformer e) tl) ++
                          [tApp (geti_info "args" e 0) (rels_of "arglambda" e)])
                    end
                  | _ => todo end in
                mktProd (Savelist "args") na e (fun e => type_rename_transformer e t1)
                  (fun e => kptProd NoSave the_name e (fun e => aux_nested e t1) t)
              end
            (**********************)
            | _ => kptProd (Savelist "args") na e
                    (fun e => type_rename_transformer e t1)
                    t
            end
          in
          let transformer_args args (t:term): extrainfo -> term :=
            fold_right (
              fun arg t => auxarg arg t
              ) (transformer_result t) args
          in
          (*ATTENTION: in the quotation of inductive types, the args of constuctor is saved in reverse order*)
          transformer_args (rev ctr.(cstr_args)) return_type e
        in
        match b with
        | [] => t e
        | ctr :: l =>
            mktProd NoSave the_name e
              (fun e => auxctr e ctr i)
              (fun e => Ffix e l t (i+1))
        end
      in
      Ffix e b t 0
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
    it_kptProd (Some "params") (params) initial_info $
      fun e =>
        (*forall P:?, ?*)
        mktProd (Saveitem "P") prop_name e
          (*type of P: forall (i1:Ind1) ... (im:Indm), T A1 ... Ak i1 ... im -> Prop*)
          (fun e =>
            (*forall (i1:Ind1) ... (im:Indm)*)
             it_mktProd (Some "indices") (indices) e $
             fun e => tProd the_name
                (*T A1 ... Ak i1 ... im*)
                (tApp (tInd the_inductive [])
                  (rels_of "params" e
                    (* ++ rels_of "no_uniform_params" e  *)
                    ++ rels_of "indices" e)
                )
                (tSort sProp) (*Prop*)
            )
          (**)
          (fun e =>
            (*see details in the [aux] above*)
            aux e body.(ind_ctors)
              (fun e =>
                (*forall (i1:Ind1) ... (im:Indm),
                  forall (x:T A1 ... Ak i1 ... im), P i1 ... im x*)
                it_mktProd (Some "indices") (indices) e $
                  fun e =>
                    mktProd (Saveitem "x") the_name e
                      (*type of x: T A1 ... Ak i1 ... im*)
                      (fun e =>
                        tApp (tInd the_inductive [])
                          (rels_of "params" e ++ rels_of "indices" e)
                        )
                      (*P i1 ... im x*)
                      (fun e => tApp (rel_of "P" e)
                        (rels_of "indices" e ++ [rel_of "x" e]))
            ))
    .


(****************************************************************)
(*for mutual inductive type*)

Fixpoint fold_right_i_aux {A B : Type} (f : B -> nat -> A -> A) i (l:list B) (a0 : A) :=
  match l with
  | [] => a0
  | b :: l' => f b i (fold_right_i_aux f (S i) l' a0 )
  end.

Definition GenerateIndp_mutual (kername : kername) (ty :  mutual_inductive_body) : term :=
    let params := ty.(ind_params) in
    let initial_info := make_initial_info kername ty in
    let bodies := ty.(ind_bodies) in
    let n_ind := length ty.(ind_bodies) in
    let (params, no_uniform_params) := SeperateParams kername ty in

    let aux (e:extrainfo) (b:list constructor_body) (j:nat) (t:extrainfo -> term) :term :=
      let fix Ffix e b (t:extrainfo -> term) i :=
        let auxctr (e:extrainfo) (ctr:constructor_body) i : term :=
          let constructor_current :=
            tConstruct {| inductive_mind := kername; inductive_ind := j |} i [] in
          let cstr_type := ctr.(cstr_type) in
          let return_type: term :=
            (fix Ffix t :=
              match t with
              | tProd _ _ t => Ffix t
              | _ => t
              end ) cstr_type
          in
          let transformer_result (t:term) :extrainfo -> term := fun e =>
            match t with
            | tApp (tRel i) tl =>
              match is_recursive_call_gen e i with
              | Some kk =>
                tApp
                  (geti_info "P" e kk)
                  (let tl := n_tl tl (length params) in
                    (map (type_rename_transformer e) tl)
                      ++
                      [
                        tApp constructor_current
                        (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "args" e)
                        ])
              | None => todo (*must be an error*)
              end
            | tRel i =>
              match is_recursive_call_gen e i with
              | Some kk =>
                tApp
                  (geti_info "P" e kk)
                  [ tApp constructor_current
                    (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "args" e)
                  ]
              | None => todo (*must be an error*)
              end
            | _ => todo end (*must be an error*)
          in
          let auxarg arg (t:extrainfo->term) :extrainfo -> term :=
            let t1 := arg.(decl_type) in
            let na := arg.(decl_name) in
            fun e =>
            match t1 with
            | tRel i =>
              match is_recursive_call_gen e i with
              | Some kk =>
                mktProd (Savelist "args") na e
                  (fun e =>
                    (tInd
                      {| inductive_mind := kername; inductive_ind := (*todo*) n_ind -1 - kk |}
                      [])
                  )
                  (fun e =>
                    kptProd NoSave the_name e
                      (fun e =>
                        tApp (geti_info "P" e kk) (*tRel 0*)[geti_info "args" e 0])
                      t)
              | None =>
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1)
                  t
              end
            | tApp (tRel i) tl =>
              match is_recursive_call_gen e i with
              | Some kk =>
                mktProd (Savelist "args") na e
                  (fun e =>
                    tApp
                      (tInd
                        {| inductive_mind := kername; inductive_ind := (*todo*) n_ind -1 - kk |}
                        [])
                     (map (type_rename_transformer e) tl))
                  (fun e =>
                    kptProd NoSave the_name e
                      (fun e => tApp
                        (geti_info "P" e kk)
                        (let tl := n_tl tl (length params) in
                          (map (type_rename_transformer e) tl) ++ [(*tRel 0*)(geti_info "args" e 0)])
                      ) t)
              | None =>
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1)
                  t
              end
            (*****************************************)
            | tProd na _ _ =>
              match check_return_type t1 e with
              | None => kptProd (Savelist "args") na e (fun e => type_rename_transformer e t1) t
              | Some _ =>
                let fix aux_nested e t1 :=
                  match t1 with
                  | tProd na ta tb =>
                    kptProd (Savelist "arglambda") na e
                      (fun e => type_rename_transformer e ta) (fun e => aux_nested e tb)
                  | tRel i =>
                    match is_recursive_call_gen e i with
                    | None => todo
                    | Some kk =>
                      tApp (geti_info "P" e kk)
                        [tApp (geti_info "args" e 0) (rels_of "arglambda" e)]
                    end
                  | tApp (tRel i) tl =>
                    match is_recursive_call_gen e i with
                    | None => todo
                    | Some kk =>
                      tApp (geti_info "P" e kk)
                        (let tl := n_tl tl (length params) in
                          (map (type_rename_transformer e) tl) ++
                          [tApp (geti_info "args" e 0) (rels_of "arglambda" e)])
                    end
                  | _ => todo end in
                mktProd (Savelist "args") na e (fun e => type_rename_transformer e t1)
                  (fun e => kptProd NoSave the_name e (fun e => aux_nested e t1) t)
              end
            (*****************************************)
            | _ => kptProd (Savelist "args") na e
                    (fun e => type_rename_transformer e t1)
                    t
            end
          in
          let transformer_args args (t:term): extrainfo -> term :=
            fold_right (
              fun arg t => auxarg arg t
              ) (transformer_result t) args
          in
          transformer_args (rev ctr.(cstr_args)) return_type e
        in
        match b with
        | [] => t e
        | ctr :: l =>
            mktProd NoSave the_name e
            (
              fun e =>
              it_kptProd (Some "no_uniform_params") (no_uniform_params) e $
              fun e => auxctr e ctr i)
            (fun e => Ffix e l t (i+1))
        end
      in
      Ffix e b t 0
    in
    let mainbody := hd todo bodies in
    let indices_main := mainbody.(ind_indices) in
    let the_inductive_main := {| inductive_mind := kername; inductive_ind := 0|} in

    it_kptProd (Some "params") (params) initial_info $
      fold_right_i_aux (
        fun body i t => fun e =>
          let the_inductive := {| inductive_mind := kername; inductive_ind :=i |} in
          let indices := body.(ind_indices) in
          mktProd (Savelist "P") prop_name e
            (fun e =>
            it_kptProd (Some "no_uniform_params") (no_uniform_params) e $
            fun e => it_mktProd (Some "indices") (indices) e $
              fun e => tProd the_name
                (tApp (tInd the_inductive [])
                 (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e))
                (tSort sProp)
            ) t
      ) 0 bodies
        (fold_right_i_aux
          (fun body i t => fun e => aux e body.(ind_ctors) i t)
          0 bodies
          (fun e =>
            it_kptProd (Some "no_uniform_params") (no_uniform_params) e $
            fun e => it_mktProd (Some "indices") (indices_main) e $
              fun e =>
                mktProd (Saveitem "x") the_name e
                  (fun e =>
                    tApp (tInd the_inductive_main [])
                      (rels_of "params" e ++ rels_of "no_uniform_params" e ++ rels_of "indices" e))
                  (fun e => tApp (geti_info "P" e (n_ind - 1 (*todo*)))
                    (rels_of "no_uniform_params" e ++ rels_of "indices" e ++ [rel_of "x" e])))
        )
    .






Notation "'$let' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
                                     (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

Notation "'try' '$let' ' x ':=' c1 'in' c2 'else' c3" := (@bind _ _ _ _ c1 (fun y =>
                                                              (match y with x => c2
                                                                       | _ => c3
                                                               end)))
                                         (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

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

