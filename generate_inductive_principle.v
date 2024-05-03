Require Import BasePrelude.

(* From MetaCoq Require Export bytestring. *)
Global Open Scope bs.


(* Print nat_ind. *)
(*
Check $quote (forall P : nat -> Prop,

  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n). *)

Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).


Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.

(* Axiom print_context : extrainfo -> forall {A}, A.
Axiom printi : nat -> forall {A}, A . *)

Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.


(* Notation "'$tProd' save na e t1 t2" := (mktProd save na e (fun e => t1) (fun e => t2)) (at level 99). *)

(*works for type not mutual inductive*)
Definition GenerateIndp (na : kername) (ty :  mutual_inductive_body) : term :=
    let params := ty.(ind_params) in
    let initial_info :=  make_initial_info na ty in
    (* suppose single inductive body*)
    let body :=
      match ty.(ind_bodies) with
      | [] => todo
      | body :: _ => body
      end
    in
    let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
    let indices := body.(ind_indices) in

    let aux (e:extrainfo) (b:list constructor_body) (t:extrainfo -> term) :term :=
      let fix Ffix e b (t:extrainfo -> term) i :=

        (* build the type of a type constructor *)
        (* take nat, 'S : nat -> nat' for example *)
        (* ~~~~> forall (n:nat), P n -> P (S n) *)
        let auxctr (e:extrainfo) (ctr:constructor_body) i : term :=
          let constructor_current := tConstruct the_inductive i [] in
          let cstr_type := ctr.(cstr_type) in
          (*get the return type of the type constructor*)
          (*nat*)
          let return_type: term :=
            (fix Ffix t :=
              match t with
              | tProd _ _ t => Ffix t
              | _ => t
              end ) cstr_type
          in
          (*transforme the return type of constructor*)
          (*~~~> P (S n)*)
          let transformer_result (t:term) :extrainfo -> term := fun e =>
            match t with
            | tApp (tRel i) tl =>
              match is_recursive_call_gen e i with
              | Some _ =>
                  tApp
                  (rel_of "P" e)
                  (let tl := n_tl tl (length params) in
                    (map (type_rename_transformer e) tl)
                      ++
                      [
                        tApp constructor_current
                          (rels_of "params" e ++ rels_of "args" e)
                      ])
              | None => todo (*must be an error*)
              end
            | tRel i =>
              match is_recursive_call_gen e i with
              | Some _ =>
                tApp
                  (rel_of "P" e)
                  [ tApp constructor_current
                      (rels_of "params" e ++ rels_of "args" e) ]
              | None => todo (*must be an error*)
              end
            | _ => todo end (*must be an error*)
          in
          (*transforme the argument*)
          (*~~~> forall (n:nat), P n*)
          let auxarg arg (t:extrainfo->term) :extrainfo -> term :=
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
                      (fun e => tApp (rel_of "P" e) [tRel 0])
                      t)
              | None =>
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1)
                  t
              end
            | tApp (tRel i) tl =>
              match is_recursive_call_gen e i with
              | Some _ =>
                mktProd (Savelist "args") na e
                  (fun e =>
                    tApp (tInd the_inductive []) (map (type_rename_transformer e) tl))
                  (fun e =>
                    kptProd NoSave the_name e
                      (fun e => tApp
                        (rel_of "P" e)
                        (let tl := n_tl tl (length params) in
                          (map (type_rename_transformer e) tl) ++ [tRel 0])
                      ) t)
              | None =>
                kptProd (Savelist "args") na e
                  (fun e => type_rename_transformer e t1)
                  t
              end
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
            mktProd NoSave the_name e (fun e => auxctr e ctr i)
              (fun e => Ffix e l t (i+1))
        end
      in
      Ffix e b t 0
    in

    it_kptProd (Savelist "params") (rev params) initial_info $
      fun e =>
        mktProd (Saveitem "P") prop_name e
          (fun e => it_mktProd (Savelist "indices") (rev indices) e $
             fun e => tProd the_name
                (if is_empty params && is_empty indices then tInd the_inductive []
                 else tApp (tInd the_inductive []) (rels_of "params" e ++ rels_of "indices" e)
                )
                (tSort sProp)
            )
          (fun e =>
            aux e body.(ind_ctors)
              (fun e =>
                it_mktProd (Savelist "indices") (rev indices) e $
                  fun e =>
                    mktProd (Saveitem "x") the_name e
                      (fun e =>
                        if is_empty params && is_empty indices then tInd the_inductive []
                        else tApp (tInd the_inductive []) (rels_of "params" e ++ rels_of "indices" e)
                       )
                      (fun e => tApp (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
            ))
    .


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
                          (rels_of "params" e ++ rels_of "args" e)
                      ])
              | None => todo (*must be an error*)
              end
            | tRel i =>
              match is_recursive_call_gen e i with
              | Some kk =>
                tApp
                  (geti_info "P" e kk)
                  [ tApp constructor_current
                      (rels_of "params" e ++ rels_of "args" e) ]
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
            mktProd NoSave the_name e (fun e => auxctr e ctr i)
              (fun e => Ffix e l t (i+1))
        end
      in
      Ffix e b t 0
    in
    let mainbody := hd todo bodies in
    let indices_main := mainbody.(ind_indices) in
    let the_inductive_main := {| inductive_mind := kername; inductive_ind := 0|} in

    it_kptProd (Savelist "params") (rev params) initial_info $
      fold_right_i_aux (
        fun body i t => fun e =>
          let the_inductive := {| inductive_mind := kername; inductive_ind :=i |} in
          let indices := body.(ind_indices) in
          mktProd (Savelist "P") prop_name e
            (fun e => it_mktProd (Savelist "indices") (rev indices) e $
              fun e => tProd the_name
                (tApp (tInd the_inductive []) (rels_of "params" e ++ rels_of "indices" e))
                (tSort sProp)
            ) t
      ) 0 bodies
        (fold_right_i_aux
          (fun body i t => fun e => aux e body.(ind_ctors) i t)
          0 bodies
          (fun e =>
            it_mktProd (Savelist "indices") (rev indices_main) e $
              fun e =>
                mktProd (Saveitem "x") the_name e
                  (fun e => tApp (tInd the_inductive_main []) (rels_of "params" e ++ rels_of "indices" e))
                  (fun e => tApp (geti_info "P" e (n_ind - 1 (*todo*))) (rels_of "indices" e ++ [rel_of "x" e])))
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
        | Some name => tmDefinitionRed name (Some hnf) r ;; ret tt
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

