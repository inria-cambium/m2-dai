Load BasePrelude.


(* Print nat_ind. *)
(*
Check $quote (forall P : nat -> Prop,

  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n). *)

Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).


Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.

Axiom print_context : extrainfo -> forall {A}, A.
Axiom printi : nat -> forall {A}, A .

Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

(*works for type with parameter/indice, not mutual inductive*)
Definition GenerateIndp (na : kername) (ty :  mutual_inductive_body) : term :=
    let params := ty.(ind_params) in
    let initial_info := add_T empty_info ty.(ind_bodies) in
    (* suppose single inductive body*)
    let body :=
      match ty.(ind_bodies) with
      | [] => todo
      | body :: _ => body
      end
    in
    let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
    let indices := body.(ind_indices) in

    let fix aux (e:extrainfo) (b:list constructor_body) (t:extrainfo -> term) :term :=
      let fix Ffix e b (t:extrainfo -> term) i :=
        let auxctr (e:extrainfo) (ctr:constructor_body) i : term :=
          let constructor_current := tConstruct the_inductive i [] in
          let cstr_type := ctr.(cstr_type) in
          let cstr_type := (*get rid of the parameter types*)
            fold_left (
              fun x _ => match x with tProd _ _ t => t | _ => todo end
            ) params cstr_type
          in
          let fix transformer_args e t: term :=
            match t with
            | tProd na t1 t2 =>
                match t1 with
                | tRel i =>
                    kptProd (Some "args") na e
                      (fun e => type_rename_transformer e (tRel i))
                      (fun e => transformer_args e t2)
                | tApp (tRel i) tl =>
                  match is_recursive_call_gen e i with
                  | Some j =>
                    mktProd (Some "args") na e
                      (fun e =>
                        tApp (tInd the_inductive []) (map (type_rename_transformer e) tl)
                      )
                      (fun e =>
                        kptProd None the_name e
                          (fun e => tApp
                            (rel_of "P" e)
                            (let tl := n_tl tl (length params) in
                              (map (type_rename_transformer e) tl) ++ [tRel 0]
                              )
                          )
                          (fun e => transformer_args e t2))
                  | None =>
                    kptProd (Some "args") na e
                      (fun e => type_rename_transformer e t1)
                      (fun e => transformer_args e t2)
                  end
                | _ => kptProd (Some "args") na e
                        (fun e => type_rename_transformer e t1)
                        (fun e => transformer_args e t2)
                end
            | tApp (tRel i) tl =>
                match is_recursive_call_gen e i with
                | Some kk =>
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
            | _ => t
            end
          in
          transformer_args e cstr_type
        in
        match b with
        | [] => t e
        | ctr :: l =>
            mktProd None the_name e (fun e => auxctr e ctr i)
              (fun e => Ffix e l t (i+1))
        end
      in
      Ffix e b t 0
    in

    it_kptProd (Some "params") (rev params) initial_info $
      fun e =>
        mktProd None prop_name e
          (fun e => it_mktProd (Some "indices") (rev indices) e $
             fun e => tProd the_name
                (tApp (tInd the_inductive []) (rels_of "params" e ++ rels_of "indices" e))
                (tSort sProp)
            )
          (fun e =>
            aux e body.(ind_ctors)
              (fun e =>
                it_mktProd (Some "indices") (rev indices) e $
                  fun e =>
                    mktProd None the_name e
                      (fun e => tApp (tInd the_inductive []) (rels_of "params" e ++ rels_of "indices" e))
                      (fun e => tApp (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
            ))
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
      let id := GenerateIndp kn mind in
      $let u := tmUnquote id in
      $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; ret tt
        | None => tmPrint r
        end
    | _ => tmFail "no inductive"
    end.

Notation "'Derive' 'InductivePrinciple' a 'as' id" := (generate_indp a (Some id)) (at level 0).

