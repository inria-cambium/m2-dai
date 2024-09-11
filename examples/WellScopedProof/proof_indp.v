Require Import MetaCoq.Programming.
Require Import WellScopedProof.api_change.
Require Import WellScopedProof.indp.
Require Import WellScopedProof.baseproof List.


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

Lemma lem_auxarg {n k l} arg the_inductive (params:context) (t:infolocal -> term) e:
  closedn k (decl_type arg) ->
  (* True -> *)
  (forall n', forall e', eprop n' (S k) (replace_info_len (Savelist "args") l) e' -> closedn n' (t e')) ->
  eprop n k l e ->
  has_info l "P" 1 ->
  closedn n (auxarg arg the_inductive params t e).
Proof.
  intros H H2 H3 H4.
  unfold auxarg.
  destruct arg as [argname argbody arg]. simpl in H.
  simpl.
  destruct arg.
  + destruct (is_rec_call e n0).
    ++ eapply lem_mktProd. exact H3. auto. intros.
       eapply lem_kptProd. exact H0.
       - change (closedn (S n) (rel_of "P" e0) && forallb (closedn (S n)) [get_info_last "args" e0]).
         apply andb_and. split. eapply lem_rel_of. exact H0. eapply lem_has_info_within1. 2:auto. 2: exact H4. auto.
         apply forallb_Forall. constructor. 2:auto.
         eapply lem_get_info_last. exact H0. eapply lem_within_replace.
       - intros. eapply H2. auto.
    ++ eapply lem_kptProd. exact H3.
       eapply lem_mapt. exact H3. auto.
       intros. eapply H2. auto.
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + destruct arg. pose (H' := lem_app_closed H).
    ++ destruct (is_rec_call e n0).
       -eapply lem_mktProd. exact H3. simpl.
       -- apply forallb_Forall. apply Forall_map. apply Forall_forall. intros.
          eapply lem_mapt. exact H3. eapply H'. auto.
       -- intros. eapply lem_kptProd. exact H0.
          +++ change (closedn (S n) (rel_of "P" e0) &&
             forallb (closedn (S n)) (map (mapt e0) (n_tl args #|params|) ++
              [get_info_last "args" e0])).
              apply andb_and. split. eapply lem_rel_of. exact H0. eapply lem_has_info_within1. 3:exact H4. auto. auto.
              apply forallb_Forall. apply app_Forall.
              --- apply Forall_map. apply Forall_forall. intros.
                  eapply lem_mapt. exact H0. eapply H'.
                  eapply lem_ntl1. exact H1.
              --- constructor. 2:auto. eapply lem_get_info_last. exact H0. apply lem_within_replace.
          +++ intros. apply H2. auto.

        - refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
    ++ refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
  + refine (lem_kptProd _ _ _ _ _ H3 (lem_mapt _ _ H3 H) (H2 _)).
Qed.

Lemma lem_transformer_result {n k l} cstrindices constructor_current e :
  has_info l "P" 1 ->
  Forall (closedn k) cstrindices ->
  closedn n constructor_current ->
  eprop n k l e ->
  closedn n (transformer_result cstrindices constructor_current e).
Proof.
  intros.
  unfold transformer_result.
  change (closedn n (rel_of "P" e) &&
    forallb (closedn n)
      (map (mapt e)
          (cstrindices) ++
        [tApp constructor_current
          (rels_of "params" e ++ rels_of "args" e)])
  ).
  apply andb_and. split.
  + eapply lem_rel_of. exact H2. eapply lem_has_info_within0. 2:exact H. auto.
  + apply forallb_Forall. apply app_Forall.
    ++ apply Forall_map. apply Forall_forall. intros x H8.
       eapply lem_mapt. exact H2.
       rewrite Forall_forall in H0.
       specialize (H0 x H8). auto.
    ++ constructor. 2:auto.
       simpl. apply andb_and. split. auto. apply forallb_Forall. apply app_Forall.
       - eapply lem_rels_of. exact H2.
       - eapply lem_rels_of. exact H2.
Qed.

Lemma lem_Ffix_args {n k l} the_inductive params
  args e t :
  has_info (addl l (Some "args") 0) "P" 1 ->
  eprop n k (addl l (Some "args") 0) e ->
  Is_closed_context k args ->
  (forall n' e', eprop n' (k + #|args|) (addl l (Some "args") #|args|) e'-> closedn n' (t e')) ->
  closedn n (Ffix_args the_inductive params args t e).
Proof.
  intros. revert H2. revert t.
  induction args.
  - simpl. intros. eapply H2. simpl. simpl in H0. assert (k=k+0); auto. rewrite <- H3. auto.
  - simpl. intros.
    eapply IHargs.
    inversion H1. auto.
    inversion H1.
    intros. eapply lem_auxarg. exact H7. auto. 2: exact H8.
    intros. apply H2. simpl in H9. assert (S (k + #|args|) = k + S #|args|); auto. rewrite <- H10. auto.
    auto.
Qed.


Lemma lem_auxctr {n k l} i ctr the_inductive params e :
  Is_closed_constructor k ctr ->
  eprop n k (addl l (Some "args") 0) e ->
  has_info (addl l (Some "args") 0) "P" 1 ->
  closedn n (auxctr i ctr the_inductive params e).
Proof.
  intros.
  unfold auxctr.
  eapply lem_Ffix_args. exact H1. exact H0.
  inversion H. auto.
  intros.
  eapply lem_transformer_result. 4:exact H2. auto.
  inversion H as [_ _ H03]. exact H03. auto.
Qed.

Lemma lem_Ffix_ctrs' {n k l} i the_inductive params b t e:
  has_info l "P" 1 ->
  eprop n k l e ->
  Forall (fun ctor => Is_closed_constructor k ctor) b ->
  (forall n', forall e', eprop n' k l e' -> closedn n' (t e')) ->
  closedn n (Ffix_ctrs' i the_inductive params b t e).
Proof.
  revert i. revert t. revert n. revert e.
  induction b.
  + simpl. intros.
    apply H2. auto.
  + intros. eapply lem_mktProd.
    exact H0. eapply lem_auxctr. inversion H1. exact H5.
    eapply lem_eprop. exact H0. auto.
    intros. fold Ffix_ctrs'. eapply IHb. auto. auto. inversion H1; auto.
    intros. apply H2. auto.
Qed.

(* Lemma lem_Ffix_ctrs {n k l} i the_inductive params b t e:
  has_info l "P" 1 ->
  eprop n k l e ->
  Forall (fun ctor => Is_closed_constructor k ctor) b ->
  (forall n', forall e', eprop n' k l e' -> closedn n' (t e')) ->
  closedn n (Ffix_ctrs i the_inductive params b t e).
Proof.
  revert i. revert t.
  induction b.
  + simpl. intros.
    apply H2. auto.
  + intros. eapply IHb. auto. auto. inversion H1. auto.
    intros. eapply lem_mktProd. exact H3.
    eapply lem_auxctr. inversion H1. exact H6. eapply lem_eprop. exact H3.
    auto. intros. apply H2. auto.
Qed. *)

(****  Main Proof ***)
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
       eapply lem_Ffix_ctrs'.
       2: exact H1. auto. unfold has_info. simpl. auto.
       destruct H as [H01 H02].
       rewrite Forall_forall in H02.
       specialize (H02 (hd todo (ind_bodies ty))).
       unfold no_empty_bodies in H9.
       apply (in_hd todo) in H9.
       specialize (H02 H9). destruct H02 as [H001 H002 H003].
       auto. intros.
       eapply lemma_it_mktProd.
       - exact H2.
       - destruct H as [H01 H02].
         rewrite Forall_forall in H02.
         specialize (H02 (hd todo (ind_bodies ty))).
         unfold no_empty_bodies in H9.
         apply (in_hd todo) in H9.
         specialize (H02 H9). destruct H02 as [H001 _ _].
         auto.
       - intros.
         eapply lem_mktProd.
         -- exact H3.
         -- simpl.
            rewrite <- forallb_Forall.
            apply app_Forall.
            --- eapply lem_rels_of.
                exact H3.
            --- eapply lem_rels_of.
                exact H3.
         -- intros.
            change (
              closedn
                (S (n' + #|ind_indices (hd todo (ind_bodies ty))|))
                (rel_of "P" e3)
              &&
              forallb
                (closedn
                  (S (n' + #|ind_indices (hd todo (ind_bodies ty))|))
                ) (rels_of "indices" e3 ++ [rel_of "x" e3])
            ).
            apply andb_and.
            split.
            --- eapply lem_rel_of.
                exact H4. simpl.
                unfold within_info.
                simpl. auto.
            --- eapply forallb_Forall.
                eapply app_Forall.
                +++ eapply lem_rels_of.
                    exact H4.
                +++ constructor. 2:auto.
                    eapply lem_rel_of.
                    exact H4. unfold within_info.
                    simpl. auto.
Qed.
