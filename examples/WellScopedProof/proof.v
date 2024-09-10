Require Import MetaCoq.Programming.
Require Import WellScopedProof.baseproof.
Global Open Scope bs.

(*This is an example of using BasePrelude:
  generate the type of induction principle of any inductive type*)


Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.


(* Fixpoint n_tl {A} (l:list A) n :=
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



(*transforme the return type of constructor*)
(*'cons : ... -> vec A (S n)'   ~~~>   P (S n) (cons A a n v)
                    ^^^^^^^^^^                                *)
Definition transformer_result ctr constructor_current :infolocal -> term := fun e =>
  tApp (rel_of "P" e)
    (
      (map (mapt e) ctr.(cstr_indices))
      ++
      [tApp constructor_current
        (rels_of "params" e ++ rels_of "args" e)]
    ).


Definition aux (b:list constructor_body) the_inductive params (e:infolocal) (t:infolocal -> term) : term :=
  let auxctr (i:nat) (ctr:constructor_body) : infolocal -> term :=
    let constructor_current := tConstruct the_inductive i [] in
    let cstr_type := ctr.(cstr_type) in
    fold_left_ie (fun _ arg t => auxarg arg the_inductive params t) ctr.(cstr_args)
      (transformer_result ctr constructor_current)
  in
  fold_right_ie
    (fun i a t e => mktProd NoSave e the_name (auxctr i a e) t)
    b t e. *)


Definition GenerateIndp (na : kername) (ty :  mutual_inductive_body) : term :=
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
  (* e <- aux body.(ind_ctors) the_inductive params e;; *)
    e <- it_mktProd_default (Some "indices") e (indices);;
    e <- mktProd (Saveitem "x") e the_name
          (tApp (tInd the_inductive [])
              (rels_of "params" e ++ rels_of "indices" e)
            );;
    (tApp (rel_of "P" e) (rels_of "indices" e ++ [rel_of "x" e]))
  .

Goal forall ty, forall kn,
  no_empty_bodies ty ->
  Is_closed_mutual_ind_body ty ->
  closedn 0 (GenerateIndp kn ty).
Proof.
  intros ty kn H9 H.
  unfold GenerateIndp.
  eapply lemma_it_kptProd.
  + eapply lem_initial. auto.
  + destruct H. auto.
  + intros e0 H0.
    eapply lem_mktProd.
    ++ exact H0.
    ++ eapply lemma_it_mktProd.
      - exact H0.
      - destruct H as [H1 H2].
        rewrite Forall_forall in H2.
        specialize (H2 (hd todo (ind_bodies ty))).
        unfold no_empty_bodies in H9.
        apply (in_hd todo) in H9.
        specialize (H2 H9).
        destruct H2 as [hindice _ _ ]. auto.
      - intros.
        simpl. apply andb_and. split. 2:auto.
        rewrite <- forallb_Forall.
        apply app_Forall.
        -- eapply lem_rels_of.
           exact H1.
        -- eapply lem_rels_of.
           exact H1.
    ++ intros.
       eapply lemma_it_mktProd.
       - exact H1.
       - destruct H as [H01 H02].
         rewrite Forall_forall in H02.
         specialize (H02 (hd todo (ind_bodies ty))).
         unfold no_empty_bodies in H9.
         apply (in_hd todo) in H9.
         specialize (H02 H9). destruct H02 as [H001 _ _].
         auto.
       - intros.
         eapply lem_mktProd.
         -- exact H2.
         -- simpl.
            rewrite <- forallb_Forall.
            apply app_Forall.
            --- eapply lem_rels_of.
                exact H2.
            --- eapply lem_rels_of.
                exact H2.
         -- intros.
            change (
              closedn (S
              (S (0 + #|ind_params ty|) +
               #|ind_indices (hd todo (ind_bodies ty))|))
              (rel_of "P" e3)
              &&
              forallb (closedn (S
              (S (0 + #|ind_params ty|) +
               #|ind_indices (hd todo (ind_bodies ty))|))
              ) (rels_of "indices" e3 ++ [rel_of "x" e3])
            ).
            apply andb_and.
            split.
            --- eapply lem_rel_of.
                exact H3. simpl.
                unfold within_info.
                simpl. auto.
            --- eapply forallb_Forall.
                eapply app_Forall.
                +++ eapply lem_rels_of.
                    exact H3.
                +++ constructor. 2:auto.
                    eapply lem_rel_of.
                    exact H3. unfold within_info.
                    simpl. auto.
Qed.



(* Definition kn_myProjT2 :=
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


MetaCoq Run Derive InductivePrinciple nat as "indp_nat".
Print indp_nat.


Inductive myvec (A:Type) : nat -> Type :=
 | myvnil : myvec A 0
 | myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
MetaCoq Run Derive InductivePrinciple myvec as "indp_myvec".
Print indp_myvec.


Inductive myvec2 (A:Type) : nat -> Type :=
 | myvnil2 : myvec2 A 1
 | myvcons2 (x:A) (n:nat) (l:list A) (v1 v2:myvec2 A n) : myvec2 A (S n).
MetaCoq Run Derive InductivePrinciple myvec2 as "indp_myvec2".
Print indp_myvec2.

Inductive myterm (A B:Type) : nat -> list A -> list B-> Type :=
  | mynat : myterm A B 0 [] []
  | mynewterm (a:A) (b:B) (n:nat) (l:list A) (l':list B) (v:myterm A B n l l') : myterm A B (S n) (a::l) (b::l')
  .
MetaCoq Run Derive InductivePrinciple myterm as "indp_myterm".
Print indp_myterm. *)

(* Print it_kptProd_default. *)





