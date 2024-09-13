Require Import MetaCoq.Programming.
Require Import WellScopedProof.api_change.
Require Import WellScopedProof.indp.
Require Import WellScopedProof.baseproof List.
Import Lia.


Lemma lem_ntl0 {A} (t:A) tl: In t (List.tl tl) -> In t tl.
  induction tl.
  - simpl. auto.
  - intro. simpl in H. simpl. right. auto.
Qed.

Lemma lem_ntl1 {A} (n:nat) (t:A) (tl:list A) : In t (n_tl tl n) -> In t tl.
  induction n.
  - auto.
  - intro. simpl in H.
  assert (In t (n_tl tl n)). eapply lem_ntl0. auto.
  exact (IHn H0).
Qed.

(*only used for tProd term, other case is trivial*)
Lemma term_ind_simpl :
    forall P : term -> Prop,
       (forall n : nat, P (tRel n)) ->
       (forall id : ident, P (tVar id)) ->
       (forall (ev : nat) (args : list term), P (tEvar ev args)) ->
       (forall s : sort, P (tSort s)) ->
       (forall t : term,
        P t ->
        forall (kind : cast_kind) (v : term), P v -> P (tCast t kind v)) ->
      (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
       (forall (na : aname) (ty : term),
        P ty -> forall body : term, P body -> P (tLambda na ty body)) ->
       (forall (na : aname) (def : term),
        P def ->
        forall def_ty : term,
        P def_ty ->
        forall body : term, P body -> P (tLetIn na def def_ty body)) ->
       (forall f : term, P f -> forall args : list term, P (tApp f args)) ->
       (forall (c : kername) (u : Instance.t), P (tConst c u)) ->
       (forall (ind : inductive) (u : Instance.t), P (tInd ind u)) ->
       (forall (ind : inductive) (idx : nat) (u : Instance.t),
        P (tConstruct ind idx u)) ->
       (forall (ci : case_info) (type_info : predicate term) (discr : term),
        P discr ->
        forall branches : list (branch term),
        P (tCase ci type_info discr branches)) ->
       (forall (proj : projection) (t : term), P t -> P (tProj proj t)) ->
       (forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx)) ->
       (forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx)) ->
       (forall i : PrimInt63.int, P (tInt i)) ->
       (forall f : PrimFloat.float, P (tFloat f)) ->
       (forall (u : Level.t) (arr : list term) (default : term),
        P default ->
        forall type : term, P type -> P (tArray u arr default type)) ->
       forall t : term, P t.
Proof.
  intros.
  induction t. all:auto.
Qed.

Lemma lem_aux_nested {n k l ls nind} params narg e t1 :
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  within_info l "args" 0 ->
  eprop n k (addl l (Some "arglambda") narg) ls e ->
  closedn k t1 ->
  closedn n (aux_nested params e t1).
Proof.
  revert t1 n narg k e.
  induction t1 using term_ind_simpl.
  all : try(intros; eapply (lem_mapt _ _ H2 _)).
  + intros.
    simpl. destruct (is_rec_call e n) eqn:eq0.
    ++ eapply lem_is_rec_call in eq0. 2:exact H2.
      apply andb_and. split.
      - eapply lem_geti_info. exact H2. auto.
        pose (H' := lem_has_info_within2 H0 eq0).
        eapply lem_has_info_within0. exact H'. auto.
      - apply forallb_Forall. constructor. 2:auto.
        eapply andb_and. split.
        -- eapply lem_get_info_last. exact H2.
            eapply lem_within_info. auto. auto.
        -- apply forallb_Forall. eapply lem_rels_of. exact H2.
    ++ eapply lem_geti_rename. 1:exact H2. simpl in H3.
      apply Compare_dec.leb_complete in H3. auto.
  + intros. inversion H3. apply andb_and in H5. destruct H5.
    change (closedn n0 (
      kptProd (Savelist "arglambda") e n
       (mapt e t1_1) (fun e => aux_nested params e t1_2)
    )).
    eapply lem_kptProd.
    exact H2. eapply lem_mapt. exact H2. auto.
    intros. eapply IHt1_2. auto. auto. auto. 2:exact H5.
    simpl in H6. exact H6.
  + intros.
    unfold aux_nested.
    destruct t1.
    destruct (is_rec_call e n0) eqn:eq0.
    all : try (eapply (lem_mapt _ _ H2 H3)).
    ++ eapply lem_is_rec_call in eq0. 2:exact H2.
      apply andb_and. split.
      - eapply lem_geti_info. exact H2. auto.
        pose (H' := lem_has_info_within2 H0 eq0).
        eapply lem_has_info_within0. exact H'. auto.
      - apply forallb_Forall. apply Forall_app. split.
        fold closedn.
        eapply Forall_map.
        simpl in H3. apply andb_and in H3. destruct H3.
        eapply forallb_Forall in H4. apply Forall_forall.
        intros. eapply lem_mapt. exact H2.
        apply lem_ntl1 in H5.
        rewrite Forall_forall in H4. auto.
        fold closedn. constructor. 2:auto.
        eapply andb_and. split.
        -- eapply lem_get_info_last. exact H2.
            eapply lem_within_info. auto. auto.
        -- apply forallb_Forall. eapply lem_rels_of. exact H2.
  Unshelve. all:auto.
Qed.

Lemma lem_auxarg {n k l ls nind} arg kn (params:context) (t:infolocal -> term) e:
  closedn k (decl_type arg) ->
  (forall n', forall e', eprop n' (S k) (replace_info_len (Savelist "args") l) ls e' -> closedn n' (t e')) ->
  eprop n k l ls e ->
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  closedn n (auxarg arg kn params t e).
Proof.
  intros H H2 H3 H4 H4'.
  unfold auxarg.
  destruct arg as [argname argbody arg]. simpl in H.
  simpl.
  destruct arg.
  all : try (refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _))).
  + destruct (is_rec_call e n0) eqn:HH.
    ++ eapply lem_mktProd. exact H3. auto. intros.
        eapply lem_kptProd. exact H0.
        - change (closedn (S n) (geti_info "P" e0 n1) && forallb (closedn (S n)) [get_info_last "args" e0]).
          apply andb_and. split. eapply lem_geti_info. exact H0. eapply lem_has_info_within1. 2:auto. 2: exact H4.
          eapply (lem_is_rec_call e _ _ H3) in HH.
          eapply (lem_has_info_within2 H4' _).
          apply forallb_Forall. constructor. 2:auto.
          eapply lem_get_info_last. exact H0. eapply lem_within_replace.
        - intros. eapply H2. auto.
    ++ eapply lem_kptProd. exact H3.
        eapply lem_mapt. exact H3. auto.
        intros. eapply H2. auto.
  + destruct (check_return_type (tProd na arg1 arg2) e).
    ++ eapply lem_mktProd. exact H3.
        eapply lem_mapt. exact H3. auto.
        intros.
        eapply lem_kptProd. exact H0. 2: auto.
        eapply lem_aux_nested. 5:exact H.
      2 : exact H4'.
      2:exact (@lem_within_replace l "args").
      eapply lem_has_info. auto. auto.
      eapply lem_eprop. auto.
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + destruct arg. pose (H' := lem_app_closed H).
    all : try (refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _))).
    ++ destruct (is_rec_call e n0) eqn:eq0.
        -eapply lem_mktProd. exact H3. simpl.
        -- apply forallb_Forall. apply Forall_map. apply Forall_forall. intros.
          eapply lem_mapt. exact H3. eapply H'. auto.
        -- intros. eapply lem_kptProd. exact H0.
          +++ change (closedn (S n) (geti_info "P" e0 n1) &&
              forallb (closedn (S n)) (map (mapt e0) (n_tl args #|params|) ++
              [get_info_last "args" e0])).
              apply andb_and. split. eapply lem_geti_info. exact H0. eapply lem_has_info_within1. 3:exact H4. 2:auto.
              eapply (lem_is_rec_call e _ _ H3) in eq0.
              eapply (lem_has_info_within2 H4' eq0).
              apply forallb_Forall. apply app_Forall.
              --- apply Forall_map. apply Forall_forall. intros.
                  eapply lem_mapt. exact H0. eapply H'.
                  eapply lem_ntl1. exact H1.
              --- constructor. 2:auto. eapply lem_get_info_last. exact H0. apply lem_within_replace.
          +++ intros. apply H2. auto.
        - refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  Unshelve. auto.
Qed.

Lemma lem_transformer_result {n k l ls nind}
  cstrindices constructor_current i_ind e :
  Forall (closedn k) cstrindices ->
  closedn n constructor_current ->
  eprop n k l ls e ->
  has_info l "P" nind ->
  i_ind < nind ->
  closedn n (transformer_result cstrindices constructor_current i_ind e).
Proof.
  intros.
  unfold transformer_result.
  change (closedn n (geti_info "P" e i_ind) &&
    forallb (closedn n)
      (map (mapt e)
          (cstrindices) ++
        [tApp constructor_current
          (rels_of "params" e ++ rels_of "args" e)])
  ).
  apply andb_and. split.
  + eapply lem_geti_info. exact H1. eapply lem_has_info_within0. 2:exact H2. auto.
  + apply forallb_Forall. apply app_Forall.
    ++ apply Forall_map. apply Forall_forall. intros x H8.
        eapply lem_mapt. exact H1.
        rewrite Forall_forall in H.
        specialize (H x H8). auto.
    ++ constructor. 2:auto.
        simpl. apply andb_and. split. auto. apply forallb_Forall. apply app_Forall.
        - eapply lem_rels_of. exact H1.
        - eapply lem_rels_of. exact H1.
Qed.

Lemma lem_Ffix_args {n k l ls nind} kn params
  args e t :
  eprop n k (addl l (Some "args") 0) ls e ->
  has_info (addl l (Some "args") 0) "P" nind ->
  has_info ls "rels_of_T" nind ->
  Is_closed_context k args ->
  (forall n' e', eprop n' (k + #|args|) (addl l (Some "args") #|args|) ls e'-> closedn n' (t e')) ->
  closedn n (Ffix_args kn params args t e).
Proof.
  intros. revert H2 H3. revert t.
  induction args.
  - simpl. intros. eapply H3. simpl. simpl in H0. assert (k=k+0); auto. rewrite <- H4. auto.
  - simpl. intros.
    eapply IHargs.
    inversion H2. auto.
    inversion H2.
    intros. eapply lem_auxarg. exact H8. auto. 2: exact H9.
    intros. apply H3. simpl in H10. assert (S (k + #|args|) = k + S #|args|); auto. rewrite <- H11. auto.
    2:exact H1. auto.
Qed.

Lemma lem_auxctr {n k l ls nind} i ctr kn params i_ind e :
  Is_closed_constructor k ctr ->
  eprop n k (addl l (Some "args") 0) ls e ->
  has_info (addl l (Some "args") 0) "P" nind ->
  has_info ls "rels_of_T" nind ->
  i_ind < nind ->
  closedn n (auxctr i ctr kn params i_ind e).
Proof.
  intros.
  unfold auxctr.
  eapply lem_Ffix_args. exact H0. exact H1. auto.
  inversion H. auto.
  intros.
  eapply lem_transformer_result. 3:exact H4. 4:exact H3. 2:auto.
  inversion H as [_ _ H03]. exact H03. auto.
Qed.

Lemma lem_Ffix_ctrs' {n k l ls nind} i kn params i_ind b t e:
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  i_ind < nind ->
  eprop n k l ls e ->
  Forall (fun ctor => Is_closed_constructor k ctor) b ->
  (forall n', forall e', eprop n' k l ls e' -> closedn n' (t e')) ->
  closedn n (Ffix_ctrs' i kn params i_ind b t e).
Proof.
  revert i. revert t. revert n. revert e.
  induction b.
  + simpl. intros.
    apply H4. auto.
  + intros. eapply lem_mktProd.
    exact H2. eapply lem_auxctr. inversion H3. exact H7.
    eapply lem_eprop. exact H2. auto. 3:exact H1. auto. auto.
    intros. fold Ffix_ctrs'. eapply IHb. auto. auto. auto. exact H5. inversion H3. auto.
    intros. apply H4. auto.
Qed.

Lemma lem_Ffix_bodies_1 {n k l ls} i_ind bodies kn t e:
  (forall n' e', eprop n' k (addl l (Some "P") (i_ind + #|bodies|)) ls e' -> closedn n' (t e')) ->
  eprop n k (addl l (Some "P") i_ind) ls e ->
  Forall
    (fun ind_body =>
      Is_closed_body k ind_body)
    (bodies)
  ->
  closedn n (Ffix_bodies_1 i_ind bodies kn t e).
Proof.
  revert t. revert i_ind n l. revert e. induction bodies.
  + intros. simpl. apply H. simpl. simpl in H0.
    assert (i_ind + 0 = i_ind). auto. rewrite H2.
    auto.
  + intros. eapply lem_mktProd. exact H0.
    eapply lemma_it_mktProd. exact H0. inversion H1. inversion H4 as [H40 _ _]. auto.
    intros.
    ++ simpl. apply andb_and. split.
      - apply forallb_Forall. apply app_Forall.
        -- eapply lem_rels_of. exact H2.
        -- eapply lem_rels_of. exact H2.
      - auto.
    ++ intros.
       fold Ffix_bodies_1.
      eapply IHbodies.
      2:exact H2.
      - intros. apply H.
        simpl. simpl in H3.
        assert (S (i_ind + #|bodies|) = i_ind + S #|bodies|). auto.
        rewrite <- H4. auto.
      - inversion H1. auto.
Qed.

Lemma lem_Ffix_bodies_2 {n k l ls nind} i_ind bodies kn params t e:
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  i_ind + #|bodies| <= nind ->
  eprop n k l ls e ->
  Forall
    (fun ind_body =>
      Is_closed_body k ind_body)
    (bodies)
  ->
  (forall n', forall e', eprop n' k l ls e' -> closedn n' (t e')) ->
  closedn n (Ffix_bodies_2 i_ind bodies kn params t e).
Proof.
  revert n k i_ind t e. induction bodies.
  + simpl. intros.
    apply H4. auto.
  + intros.
    eapply lem_Ffix_ctrs'.
    2: exact H0. exact H. simpl in H1. lia. exact H2.
    inversion H3. destruct H7 as [_ H70 _]. exact H70.
    intros. fold Ffix_bodies_2. eapply IHbodies. auto. auto.
    simpl in H1. lia.
    exact H5. inversion H3. auto. auto.
Qed.


Goal forall ty, forall kn,
  no_empty_bodies ty ->
  Is_closed_mutual_ind_body ty ->
  closedn 0 (GenerateIndp kn ty).
Proof.
  intros ty kn H_no_empty H_closed.
  eapply lemma_it_kptProd.
  + eapply lem_initial. auto.
  + destruct H_closed. auto.
  + intros e0 H0.
    eapply lem_Ffix_bodies_1. 2:apply lem_eprop. 2:exact H0.
    intros. eapply lem_Ffix_bodies_2. 4:exact H.
    3 : simpl. 3: constructor.
    simpl. unfold has_info. unfold find. simpl. auto.
    unfold has_info. simpl. auto.
    inversion H_closed. auto.
    intros.
    ++ eapply lemma_it_mktProd.
       exact H1. destruct H_closed as [_ H_bodies].
       -unfold no_empty_bodies in H_no_empty.
        rewrite Forall_forall in H_bodies.
        specialize (H_bodies (hd todo (ind_bodies ty))).
        pose (H' := in_hd todo (ind_bodies ty)).
        specialize (H' H_no_empty).
        apply H_bodies in H'. inversion H'. auto.
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
           closedn
             (S (n'0 + #|ind_indices (hd todo (ind_bodies ty))|))
             (rel_of "P" e2)
           &&
           forallb
             (closedn
               (S (n'0 + #|ind_indices (hd todo (ind_bodies ty))|))
             ) (rels_of "indices" e2 ++ [rel_of "x" e2])
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
    ++ inversion H_closed. auto.
Qed.
