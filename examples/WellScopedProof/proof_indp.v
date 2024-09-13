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
       eapply lem_tApp.
      - eapply lem_geti_info. exact H2. auto.
        pose (H' := lem_has_info_within2 H0 eq0).
        eapply lem_has_info_within0. exact H'. auto.
      - constructor. 2:auto. eapply lem_tApp.
        -- eapply lem_get_info_last. exact H2.
            eapply lem_within_info. auto. auto.
        -- eapply lem_rels_of. exact H2.
    ++ eapply lem_geti_rename. exact H2. simpl in H3.
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
       eapply lem_tApp.
      - eapply lem_geti_info. exact H2. auto.
        pose (H' := lem_has_info_within2 H0 eq0).
        eapply lem_has_info_within0. exact H'. auto.
      - apply Forall_app. split.
        eapply Forall_map.
        simpl in H3. apply andb_and in H3. destruct H3.
        eapply forallb_Forall in H4. apply Forall_forall.
        intros. eapply lem_mapt. exact H2.
        apply lem_ntl1 in H5.
        rewrite Forall_forall in H4. auto.
        fold closedn. constructor. 2:auto.
        eapply lem_tApp.
        -- eapply lem_get_info_last. exact H2.
            eapply lem_within_info. auto. auto.
        -- eapply lem_rels_of. exact H2.
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
        - eapply lem_tApp.
          eapply lem_geti_info. exact H0. eapply lem_has_info_within1. 2:auto. 2: exact H4.
          eapply (lem_is_rec_call e _ _ H3) in HH.
          eapply (lem_has_info_within2 H4' _).
          constructor. 2:auto.
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
          +++ eapply lem_tApp.
              eapply lem_geti_info. exact H0. eapply lem_has_info_within1. 3:exact H4. 2:auto.
              eapply (lem_is_rec_call e _ _ H3) in eq0.
              eapply (lem_has_info_within2 H4' eq0).
              apply app_Forall.
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
  eapply lem_tApp.
  + eapply lem_geti_info. exact H1. eapply lem_has_info_within0. 2:exact H2. auto.
  + apply app_Forall.
    ++ eapply lem_rels_of. exact H1.
    ++ apply Forall_app. split. apply Forall_map. apply Forall_forall. intros x H8.
        eapply lem_mapt. exact H1.
        rewrite Forall_forall in H.
        specialize (H x H8). auto.
        constructor. 2:auto.
        eapply lem_tApp.
        auto. apply app_Forall.
        - eapply lem_rels_of. exact H1.
        - apply Forall_app. split. eapply lem_rels_of. exact H1. eapply lem_rels_of. exact H1.
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

Lemma lem_Ffix_ctrs' {n k l ls nind} no_uniform_params i kn params i_ind b t e:
  Is_closed_context k no_uniform_params ->
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  i_ind < nind ->
  eprop n k l ls e ->
  Forall (fun ctor => Is_closed_constructor (k + #|no_uniform_params|) ctor) b ->
  (forall n', forall e', eprop n' k l ls e' -> closedn n' (t e')) ->
  closedn n (Ffix_ctrs' no_uniform_params i kn params i_ind b t e).
Proof.
  revert i. revert t. revert n. revert e.
  induction b.
  + simpl. intros.
    eapply H5. exact H3.
  + intros. eapply lem_mktProd.
    exact H3. eapply lemma_it_kptProd. exact H3. auto.
    intros.
    eapply lem_auxctr. inversion H4. exact H9.
    eapply lem_eprop. exact H6. auto. 3:exact H2. auto. auto.
    intros. fold Ffix_ctrs'. eapply IHb. auto. auto. auto. auto. simpl in H6. auto. inversion H4. auto.
    intros. eapply H5. exact H7.
Qed.

Lemma lem_Ffix_bodies_1 {n k l ls} no_uniform_params i_ind bodies kn t e:
  Is_closed_context k no_uniform_params ->
  (forall n' e', eprop n' k (addl l (Some "P") (i_ind + #|bodies|)) ls e' -> closedn n' (t e')) ->
  eprop n k (addl l (Some "P") i_ind) ls e ->
  Forall
    (fun ind_body =>
      Is_closed_body (k + #|no_uniform_params|) ind_body)
    (bodies)
  ->
  closedn n (Ffix_bodies_1 no_uniform_params i_ind bodies kn t e).
Proof.
  revert t. revert i_ind n l. revert e. induction bodies.
  + intros. simpl. apply H0. simpl. simpl in H1.
    assert (i_ind + 0 = i_ind). auto. rewrite H3.
    auto.
  + intros. eapply lem_mktProd. exact H1.
    eapply lemma_it_kptProd. 2:exact H. exact H1. intros.
    eapply lemma_it_mktProd. exact H3. inversion H2. inversion H6 as [H60 _ _]. auto.
    intros.
    ++ simpl. apply andb_and. split.
      - apply forallb_Forall. apply app_Forall.
        -- eapply lem_rels_of. exact H4.
        -- apply Forall_app. split. eapply lem_rels_of. exact H4.
           eapply lem_rels_of. exact H4.
      - auto.
    ++ intros.
       fold Ffix_bodies_1.
       eapply IHbodies. auto. intros. apply H0.
       assert (S (i_ind + #|bodies|) = i_ind + S #|bodies|). auto.
       simpl. rewrite <- H5. exact H4. auto.
       inversion H2. auto.
Qed.

Lemma lem_Ffix_bodies_2 {n k l ls nind} no_uniform_params i_ind bodies kn params t e:
  Is_closed_context k no_uniform_params ->
  has_info l "P" nind ->
  has_info ls "rels_of_T" nind ->
  i_ind + #|bodies| <= nind ->
  eprop n k l ls e ->
  Forall
    (fun ind_body =>
      Is_closed_body ( k + #|no_uniform_params|) ind_body)
    (bodies)
  ->
  (forall n', forall e', eprop n' k l ls e' -> closedn n' (t e')) ->
  closedn n (Ffix_bodies_2 no_uniform_params i_ind bodies kn params t e).
Proof.
  revert n k i_ind t e. induction bodies.
  + simpl. intros.
    apply H5. auto.
  + intros.
    eapply lem_Ffix_ctrs'.
    2: exact H0. exact H. exact H1. simpl in H2. lia. exact H3.
    inversion H4. destruct H8 as [_ H80 _]. exact H80.
    intros. fold Ffix_bodies_2. eapply IHbodies. 2:auto. 2:auto.
    exact H.
    simpl in H2. lia.
    exact H6. inversion H4. auto. auto.
Qed.


Goal forall ty, forall kn,
  no_empty_bodies ty ->
  Is_closed_mutual_ind_body ty ->
  closedn 0 (GenerateIndp kn ty).
Proof.
  intros ty kn H_no_empty H_closed.
  destruct (SeperateParams kn ty) eqn : eq9.
  unfold GenerateIndp. rewrite eq9. simpl.
  pose proof (Hparams := lem_seperateparams kn ty).
  rewrite eq9 in Hparams.
  inversion H_closed as [H_closed_params H_closed_body].
  rewrite Hparams in H_closed_params.
  pose proof (H_nu_p := lem_is_closed_context3 _ _ _ H_closed_params).
  pose proof (H_u_p := lem_is_closed_context2 _ _ _ H_closed_params).
  eapply lemma_it_kptProd.
  + eapply lem_initial. auto.
  + auto.
  + intros e0 H0.
    rewrite Hparams in H_closed_body.
    rewrite app_length in H_closed_body.
    assert (H'' :  (#|ind_bodies ty| + (#|l0| + #|l|)) =
                    (#|ind_bodies ty| + #|l| + #|l0|) ). lia.
    rewrite H'' in H_closed_body.
    eapply lem_Ffix_bodies_1. exact H_nu_p. 2:apply lem_eprop. 2:exact H0.
    intros. eapply lem_Ffix_bodies_2. 5:exact H.
    auto.
    simpl. unfold has_info. unfold find. simpl. auto.
    unfold has_info. simpl. auto. auto. auto.
    ++intros.
      eapply lemma_it_kptProd. 2:exact H_nu_p. exact H1. intros.
      eapply lemma_it_mktProd.
       exact H2.
       -unfold no_empty_bodies in H_no_empty.
        rewrite Forall_forall in H_closed_body.
        specialize (H_closed_body (hd todo (ind_bodies ty))).
        pose (H' := in_hd todo (ind_bodies ty)).
        specialize (H' H_no_empty).
        apply H_closed_body in H'. inversion H'. auto.
      - intros.
        eapply lem_mktProd.
        -- exact H3.
        -- eapply lem_tApp. auto.
           apply app_Forall.
           --- eapply lem_rels_of.
               exact H3.
           --- apply Forall_app. split. eapply lem_rels_of. exact H3.
               eapply lem_rels_of. exact H3.
        -- intros. eapply lem_tApp.
            --- eapply lem_geti_info.
                exact H4. simpl.
                unfold within_info.
                simpl. auto.
            --- eapply app_Forall.
                +++ eapply lem_rels_of.
                    exact H4.
                +++ eapply app_Forall.
                    eapply lem_rels_of. exact H4.
                    constructor. 2:auto.
                    eapply lem_rel_of.
                    exact H4. unfold within_info.
                    simpl. auto.
    ++ auto.
Qed.
