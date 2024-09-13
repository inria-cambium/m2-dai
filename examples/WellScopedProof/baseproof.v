Require Import MetaCoq.Programming.
Require Import WellScopedProof.api_change.
Global Open Scope bs.
Import Lia.


Lemma lemstr: forall s1 s2 :string, String.eqb s1 s2 = true <-> s1 = s2.
  intros. rewrite String.eqb_compare. split.
  - intro.
    destruct (String.compare s1 s2) eqn:e0.
    + apply bytestring.StringOT.compare_eq. auto.
    + inversion H.
    + inversion H.
  - intro.
    apply bytestring.StringOT.compare_eq in H.
    assert (String.compare s1 s2 = Eq). auto.
    rewrite H0. auto.
Qed.

Lemma lem_app_closed {t tl n} : closedn n (tApp t tl) -> forall t', In t' tl -> closedn n t'.
Proof.
  intros.
  simpl in H. apply andb_andI in H. destruct H.
  apply forallb_Forall in H1.
  eapply Forall_forall in H1. 2:exact H0. auto.
Qed.


Section eprop_.

  Definition closed_info_n (n:nat) (e:infolocal) :=
    Forall (fun x => match x with tRel i => Nat.ltb i n | tInd _ _ => true | _ => false end)
      (map decl_type e.(renaming))
    /\
    Forall (fun '(_, l) =>
        Forall (fun x => Nat.ltb x n) (map decl_type l)
        ) e.(info)
    .

  Lemma info_lift {n m e} : closed_info_n n e -> n <= m -> closed_info_n m e.
  Proof.
    intros.
    destruct H.
    split.
    eapply Forall_impl. 2: exact H. intros. destruct a. all: auto.
    apply Compare_dec.leb_complete in H2. apply Compare_dec.leb_correct.
    lia.

    eapply Forall_impl. 2: exact H1. intros. destruct a.
    eapply Forall_impl. 2: exact H2. intros. apply Compare_dec.leb_correct.
    simpl in H3. eapply Compare_dec.leb_complete in H3.  lia.
  Qed.

  (** eprop **)
  Record eprop (n k:nat) (l ls:list (string * nat)) (e:infolocal) : Prop := mkeprop {
    ci : closed_info_n n e;
    ck : k <= #|e.(renaming)|;
    Pl : Forall2 (fun x y => x.1 = y.1 /\ #|x.2| >= y.2) e.(info) l;
    Pls : Forall2 (fun x y => x.1 = y.1 /\ #|x.2| = y.2) e.(info_source) ls;
  }.

  Fixpoint replace_add_l (l:list (string * nat)) str :=
    match l with
    | [] => [(str, 1)]
    | (name, n) :: l' =>
      if String.eqb name str then (name, S n) :: l'
      else (name, n) :: (replace_add_l l' str)
    end.

  Definition replace_info_len saveinfo (l:list (string * nat)) :=
    match saveinfo with
    | NoSave => l
    | Savelist str => replace_add_l l str
    end.

  Definition addl (l:list (string*nat)) si i :=
    match si with
    | None => l
    | Some str => (str, i) :: l end.


  Lemma lem_eprop {n k l ls} e str :
    eprop n k l ls e ->
    eprop n k (addl l (Some str) 0) ls (add_emp_info e (Some str)).
  Proof.
    intro.
    destruct H. destruct e. simpl in ci0, ck0, Pl0.
    simpl. split.
    + destruct ci0 as [ H3 H4]. simpl in H3, H4. split. simpl. auto.
      simpl. auto.
    + simpl. auto.
    + simpl. constructor. auto. auto.
    + simpl. auto.
  Qed.

End eprop_.

Section proof_within_info.

  Definition within_info l (str:string) (i:nat) :=
    match (find (fun x => String.eqb str x.1) l) with
    | Some (_, n) => i < n
    | None => i < 0 end.

  Definition has_info (l:list (string*nat)) str i :=
    match
      (find (fun x => String.eqb str x.1) l) with
    | Some (_, k) => i = k
    | None => False
    end.

  Lemma lem001 {s1 s2} l : String.eqb s1 s2 = false ->
    find
      (fun x : string × nat =>
       String.eqb s1 x.1) l
    =
    find
      (fun x : string × nat =>
      String.eqb s1 x.1)
      (replace_add_l l s2).
  Proof.
    intros.
    induction l.
    + simpl. rewrite H. auto.
    + simpl. destruct a. simpl.
      destruct (String.eqb s1 t) eqn:eq1.
      - destruct (String.eqb t s2) eqn:eq2.
        ++ apply lemstr in eq1. rewrite <- eq1 in eq2. rewrite H in eq2. inversion eq2.
        ++ simpl. rewrite eq1. auto.
      - destruct (String.eqb t s2) eqn:eq2.
        ++ simpl. rewrite eq1. auto.
        ++ simpl. rewrite eq1. auto.
  Qed.

  Lemma lem002 {s1 s2 n} l : String.eqb s1 s2 = false ->
    find
      (fun x : string × nat =>
      String.eqb s1 x.1) l
    =
    find
      (fun x : string × nat =>
      String.eqb s1 x.1)
      (addl l (Some s2) n).
  Proof.
    intros.
    induction l.
    + simpl. rewrite H. auto.
    + simpl. destruct a. simpl.
      destruct (String.eqb s1 t) eqn:eq1.
      - destruct (String.eqb t s2) eqn:eq2.
        ++ apply lemstr in eq1. rewrite <- eq1 in eq2. rewrite H in eq2. inversion eq2.
        ++ apply lemstr in eq1. rewrite <- eq1 in eq2. rewrite eq2. auto.
      - destruct (String.eqb t s2) eqn:eq2.
        ++ simpl. apply lemstr in eq2. rewrite eq2 in eq1. rewrite eq1. auto.
      ++ simpl. rewrite H. auto.
  Qed.

  Lemma lem_within_info l str n str2 n2:
    String.eqb str str2 = false ->
    within_info l str n ->
    within_info (addl l (Some str2) n2)  str n.
    Proof.
    intro HF.
    unfold within_info.
    pose (H :=  @lem002 str str2 n2 l HF).
    rewrite H. intro. auto.
  Qed.

  Lemma lem_has_info l str n str2 :
    String.eqb str str2 = false ->
    has_info l str n ->
    has_info (replace_add_l l str2) str n .
    Proof.
    intro.
    unfold has_info.
    pose (H' := @lem001 str str2 l). rewrite H'. auto. auto.
  Qed.

  Lemma lem_has_info_within0 {l nind str j}: j < nind -> has_info l str nind -> within_info l str j.
  Proof.
    unfold within_info, has_info.
    intros.
    destruct (find (fun x => String.eqb str x.1) l).
    + destruct p. lia.
    + auto.
  Qed.

  Lemma lem_has_info_within1 {nind l str1 str2 kk }:
    kk < nind -> String.eqb str1 str2 = false
    -> has_info l str1 nind
    -> within_info (replace_add_l l str2) str1 kk.
  Proof.
    intros.
    unfold has_info in H1.
    unfold within_info.
    pose proof (lem001 l H0).
    destruct (find
                (fun x : string × nat =>
                String.eqb str1 x.1) l) eqn:eq0.
    + rewrite <- H2. destruct p. lia.
    + auto.
  Qed.

  Lemma lem_has_info_within2 {str ls nind n}:
    has_info ls str nind ->
    within_info ls str n ->
    n < nind.
  Proof.
    unfold has_info.
    unfold within_info.
    destruct (find (fun x => String.eqb str x.1) ls).
    + destruct p.  lia.
    + auto.
  Qed.

End proof_within_info.


Section index_manage.

  Lemma plus_one_index_length {l} : #|plus_one_index l| = #|l|.
    induction l.
    + auto.
    + simpl. auto.
  Qed.

  Lemma lift_renaming_length {renaming}: #|renaming| = #|lift_renaming renaming|.
    induction renaming.
    - auto.
    - simpl. auto.
  Qed.

  Lemma map_plus_one: forall l, map decl_type (plus_one_index l) = map (fun x => S x) (map decl_type l).
  Proof.
    induction l.
    - auto.
    - simpl. rewrite IHl. auto.
  Qed.

  Lemma lem_plus_one_index {n} {renaming}: Forall (fun x:nat => Nat.ltb x n) (map decl_type renaming)
    -> Forall (fun x:nat => Nat.ltb x (S n)) (map decl_type (plus_one_index renaming)).
  Proof.
    intro H.
    rewrite map_plus_one.
    induction (map decl_type renaming).
    firstorder.
    simpl. inversion H.
    apply IHl in H3.
    constructor. auto. auto.
  Qed.

  Lemma lem_renaming : forall renaming0 n,
    Forall
      (fun x : term =>
        match x with
        | tRel i => Nat.ltb i n
        | tInd _ _ => true
        | _ => false
        end) (map decl_type renaming0) ->
    Forall
      (fun x : term =>
        match x with
        | tRel i => Nat.ltb i (S n)
        | tInd _ _ => true
        | _ => false
        end) (map decl_type (lift_renaming renaming0)).
  intros.
  induction renaming0.
  - simpl. auto.
  - simpl. constructor. simpl in H. inversion H.
    + destruct (decl_type a).
      all: auto.
       (* simpl. apply Compare_dec.leb_correct. apply Compare_dec.leb_complete in H2. *)
      (* lia. *)
    + inversion H. auto.
  Qed.

  Lemma S_forall: forall l n,
    Forall (fun x => Nat.ltb x n) l ->
    Forall (fun x => Nat.ltb x (S n)) (map (fun x => S x) l).
  Proof.
    intros.
    induction l.
    - auto.
    - simpl.
      inversion H.
      apply IHl in H3.
      apply Forall_cons. all: auto.
  Qed.

  Lemma lem_info0 {n:nat} info0:
    Forall
      (fun '(_, l) =>
        Forall (fun x : nat => Nat.ltb x n)
          (map decl_type l)) info0
      ->
    Forall
    (fun '(_, l) =>
      Forall (fun x : nat => Nat.ltb x (S n)) (map decl_type l))
    (map
        (fun
          x : string × list (BasicAst.context_decl nat)
        => (x.1, plus_one_index x.2)) info0).
  Proof.
    induction info0.
    - auto.
    - simpl. constructor. 2: eapply IHinfo0. 2: eapply incl_Forall. 3: exact H. 2: firstorder.
      rewrite map_plus_one.
      inversion H.
      destruct a. simpl.
      eapply S_forall. auto.
  Qed.

  Lemma lem_info {n} {na0} {s} info0:
    Forall (fun '(_, l) =>
              Forall (fun x : nat => Nat.ltb x n)
            (map decl_type l)) info0
      ->
    Forall
      (fun '(_, l) =>
      Forall (fun x : nat => Nat.ltb x (S n)) (map decl_type l))
      (replace_add_info
        (map
            (fun
              x : string
                  × list (BasicAst.context_decl nat) =>
            (x.1, plus_one_index x.2)) info0) s
        (mkdecl na0 None 0)).
  Proof.
    intro H.
    induction info0.
    - simpl. constructor. 2: auto. constructor. 2: auto. auto.
    - simpl.
      destruct (String.eqb a.1 s).
      + constructor.
        inversion H.
        -- simpl. constructor. auto. destruct a. simpl. eapply lem_plus_one_index. auto.
        -- assert (Forall
                      (fun '(_, l) =>
                      Forall (fun x : nat => Nat.ltb x n)
                        (map decl_type l)) (info0)).
          eapply incl_Forall. 2: exact H. firstorder.
          eapply lem_info0. auto.
      + constructor. inversion H.
        -- destruct a. simpl. eapply lem_plus_one_index. auto.
        -- eapply IHinfo0. inversion H. auto.
  Qed.

End index_manage.


Section proof_update.

  Lemma lemy01 {l l'}:
    Forall2
    (fun (x : string × list (BasicAst.context_decl nat))
      (y : string × nat) => x.1 = y.1 /\ #|x.2| >= y.2) l
    l' ->
    Forall2
    (fun (x : string × list (BasicAst.context_decl nat))
      (y : string × nat) => x.1 = y.1 /\ #|x.2| >= y.2)
    (map
      (fun x : string × list (BasicAst.context_decl nat) =>
        (x.1, plus_one_index x.2)) l) l'.
  Proof.
    intro. induction H.
    - auto.
    - simpl. constructor.
      + simpl. rewrite plus_one_index_length. auto.
      + auto.
  Qed.

  Lemma lemx01 {info l s na} :
    Forall2
      (fun x y => x.1 = y.1 /\ #|x.2| >= y.2)
      info l
    ->
    Forall2
      (fun x y => x.1 = y.1 /\ #|x.2| >= y.2)
      (replace_add_info
        (map
            (fun x => (x.1, plus_one_index x.2)) info) s
        (mkdecl na None 0)) (replace_add_l l s).
  Proof.
    intro.
    induction H.
    - simpl. constructor.
      + simpl. auto.
      + constructor.
    - simpl. destruct (String.eqb x.1 s) eqn:e0.
      + destruct x, y. simpl. simpl in e0.
        destruct (String.eqb t0 s) eqn:e1.
        ++ rewrite lemstr in e0, e1.
          rewrite e0. rewrite e1. simpl.
          constructor.
          +++ simpl. simpl in H. rewrite plus_one_index_length. split. auto. lia.
          +++ apply lemy01. auto.
        ++  simpl in H. destruct H. rewrite H in e0. rewrite e0 in e1. inversion e1.
      + destruct x, y. simpl in H. simpl.
        destruct (String.eqb t0 s) eqn:e1.
        ++ simpl in e0. destruct H. rewrite H in e0. rewrite e0 in e1. inversion e1.
        ++ simpl in e0. constructor.
          +++ simpl. rewrite plus_one_index_length. auto.
          +++ eapply IHForall2.
  Qed.

  Lemma lemy01' l l':
    Forall2
      (fun (x : string × list (BasicAst.context_decl nat))
        (y : string × nat) => x.1 = y.1 /\ #|x.2| = y.2) l
      l' ->
    Forall2
      (fun (x : string × list (BasicAst.context_decl nat))
        (y : string × nat) => x.1 = y.1 /\ #|x.2| = y.2)
      (map
        (fun x : string × list (BasicAst.context_decl nat) =>
          (x.1, plus_one_index x.2)) l) l'.
  Proof.
    intro H.
    induction H.
      - auto.
      - simpl. constructor.
        ++ simpl. rewrite plus_one_index_length. auto.
        ++ auto.
  Qed.

  (*update*)
  Lemma lem_update_mk {n k l ls} na e saveinfo :
    eprop n k l ls e ->
    eprop (S n) k (replace_info_len (saveinfo) l) ls
      (update_mk na e (saveinfo) ).
  Proof.
    intros. destruct H. destruct saveinfo.
    + split.
      ++ destruct ci0.
        unfold update_mk. destruct e. simpl.
        unfold closed_info_n. split. simpl. simpl in H.
        apply lem_renaming. auto.
        simpl. simpl in H0. apply lem_info. auto.
      ++ simpl. rewrite <- lift_renaming_length. auto.
      ++ simpl. apply lemx01. auto. ++ auto.
    + split.
      ++ destruct ci0.
        unfold update_mk. destruct e. simpl.
        unfold closed_info_n. split. simpl. simpl in H.
        apply lem_renaming. auto.
        simpl. simpl in H0. apply lem_info0. auto.
      ++ simpl. rewrite <- lift_renaming_length. auto.
      ++ simpl. apply lemy01. auto. ++ auto.
  Qed.

  Lemma lem_update_kp {n k l ls} na e saveinfo :
    eprop n k l ls e ->
    eprop (S n) (S k) (replace_info_len ( saveinfo) l) ls
      (update_kp na e (saveinfo) ).
  Proof.
    intros. destruct H. destruct saveinfo.
    + split.
      ++ destruct ci0.
          unfold update_mk. destruct e. simpl.
          unfold closed_info_n. split. simpl. simpl in H.
          constructor. auto. apply lem_renaming. auto.
          simpl. simpl in H0. apply lem_info. auto.
      ++ simpl. rewrite <- lift_renaming_length. lia.
      ++ simpl. apply lemx01. auto.
      ++ unfold update_kp. simpl. eapply lemy01'. auto.
    + split.
    ++ destruct ci0.
        unfold update_mk. destruct e. simpl.
        unfold closed_info_n. split. simpl. simpl in H.
        constructor. auto. apply lem_renaming. auto.
        simpl. simpl in H0. apply lem_info0. auto.
    ++ simpl. rewrite <- lift_renaming_length. lia.
    ++ simpl. apply lemy01. auto.
    ++ unfold update_kp. simpl. eapply lemy01'. auto.
  Qed.

End proof_update.


Section proof_tProd.

  (*mktProd*)
  Lemma lem_mktProd {n k l ls} saveinfo e na t1 t2 :
    eprop n k l ls e ->
    closedn n t1 ->
    (forall e0, eprop (S n) k (replace_info_len (saveinfo) l) ls e0 -> closedn (S n) (t2 e0))
    -> closedn n (mktProd (saveinfo) e na t1 t2).
  Proof.
    intros.
    unfold mktProd. unfold mktbind.
    pose (e1 := update_mk na e (saveinfo)).
    specialize (H1 e1).
    change (closedn n t1 && closedn (S n) (t2 e1)).
    apply andb_and. split. auto.
    apply H1. apply lem_update_mk. auto.
  Qed.

  (*kptProd*)
  Lemma lem_kptProd {n k l ls} saveinfo e na t1 t2 :
    eprop n k l ls e ->
    closedn n t1 ->
    (forall e0, eprop (S n) (S k) (replace_info_len (saveinfo) l) ls e0 -> closedn (S n) (t2 e0))
    -> closedn n (kptProd (saveinfo) e na t1 t2).
  Proof.
    intros.
    unfold mktProd. unfold mktbind.
    pose (e1 := update_kp na e (saveinfo)).
    specialize (H1 e1).
    change (closedn n t1 && closedn (S n) (t2 e1)).
    apply andb_and. split. auto.
    apply H1. apply lem_update_kp. auto.
  Qed.

End proof_tProd.


Section proof_rels_of.

  Lemma lem_lookup_list {n k l ls} e (str:string):
    eprop n k l ls e ->
    Forall (fun x => Nat.ltb (decl_type x) n) ((lookup_list (e.(info)) str)).
  Proof.
    intro.
    destruct e.
    simpl. destruct H.
    destruct ci0. clear H. unfold lookup_list. simpl.
    destruct
      (find
        (fun i : string × information =>
         let (na', _) := i in String.eqb str na') info) eqn:eq0.
    - destruct p. simpl in H0.
      apply find_some in eq0.
      destruct eq0.
      rewrite Forall_forall in H0.
      pose (h0 := H0 (t, i) H). simpl in h0.
      rewrite Forall_map in h0. auto.
    - auto.
  Qed.

  Lemma lem789 {A B}: forall (y:B) (l:list A) (f:A->B),
    In y (rev_map (fun x => f x) l) ->
      exists n:nat, exists x:A, y = f x.
  Proof.
    intros y l.
    induction l.
    - intros. simpl in H. auto.
    - intros. simpl in H. rewrite rev_map_spec in H.
      rewrite <- in_rev in H. simpl in H.
      destruct H. + exists 0. exists a. auto.
      + rewrite in_rev in H.
        rewrite <- rev_map_spec in H.
        eapply IHl in H. auto.
  Qed.

  Lemma lem7899 {A B}: forall (y:B) (l:list A) (f:A->B),
    In y (map (fun x => f x) l) ->
      exists n:nat, exists x:A, y = f x.
  Proof.
    intros y l.
    induction l.
    - intros. simpl in H. auto.
    - intros. simpl in H.
      destruct H. + exists 0. exists a. auto.
      + auto.
  Qed.

  Lemma lem9975 n l:
    In (tRel n)
      (map
        (fun x:BasicAst.context_decl nat =>
         tRel (decl_type x)) l)
    ->
      exists (na:aname), exists (body:option nat),
        In (mkdeclnat na body n) l.
  Proof.
    induction l.
    - intro. simpl in H. inversion H.
    - intro. simpl in H.
      destruct H.
      + exists (decl_name a).
        exists (decl_body a). simpl. left.
        inversion H. destruct a. auto.
      + specialize (IHl H).
        destruct IHl. destruct H0.
        exists x. exists x0. right. auto.
  Qed.

  Lemma lem_rels_of {n k l ls} e na:
    eprop n k l ls e ->
    Forall (fun t => closedn n t) (rels_of na e).
  Proof.
    intro.
    pose (h0 := @lem_lookup_list n k l _ e na H).
    rewrite Forall_forall in h0.
    unfold rels_of. rewrite rev_map_spec.
    apply Forall_forall.
    intros. rewrite <- in_rev in H0.
    pose (newh := lem7899 _ _ _ H0).
    destruct newh. destruct H1.
    rewrite H1. simpl.
    destruct x1 as [a b c]. simpl. simpl in H0.
    simpl in H1. rewrite H1 in H0.
    eapply lem9975 in H0.
    destruct H0. destruct H0.
    change (Nat.ltb (decl_type (mkdeclnat x1 x2 c)) n).
    eapply h0. auto.
  Qed.

End proof_rels_of.


Section proof_geti_info.

  Lemma lem8989 {n k l ls} e (str:string) (i:nat):
    eprop n k l ls e ->
    within_info l str i -> i < #|lookup_list (info e) str|.
  Proof.
    intro.
    destruct e. simpl.
    destruct H. simpl in Pl0.
    unfold within_info.
    unfold lookup_list. simpl.
    (* simpl in Pl0. simpl in H. *)
    clear ck0. clear ci0.
    induction Pl0.
    - auto.
    - destruct x, y. simpl in H. simpl.
      (* simpl. simpl in H. *)
      destruct H. rewrite H.
      destruct (String.eqb str t0) eqn:e0.
      + lia.
      + simpl in IHPl0. auto.
  Qed.

  Lemma lem_geti_info {n k l ls} e na i :
    eprop n k l ls e ->
    within_info l na i ->
    closedn n (geti_info na e i).
  Proof.
    intros.
    unfold geti_info.
    rewrite nth_nth_error.
    destruct (nth_error (rev_map decl_type (lookup_list (info e) na)) i) eqn:H1.
    -
      eapply nth_error_In in H1.
      unfold lookup_list in H1. destruct e. simpl in H1.
      destruct (find  (fun
                  i : string
                      × information
                =>
                let (na', _) := i in
                String.eqb na na') info ) eqn:e0.
    +
      eapply find_some in e0. destruct e0.
      destruct H.
      destruct ci0. simpl. simpl in H4.
      assert (let '(_,l) := p in Forall
                (fun x : nat => PeanoNat.Nat.ltb x n)
                (map decl_type l)).
      ++
        rewrite Forall_forall in H4.
        exact (H4 p H2).
      ++
        destruct p.
        rewrite Forall_forall in H5.
        apply H5.
        rewrite rev_map_spec in H1.
        rewrite <- in_rev in H1. auto.
    + inversion H1.
    -
      apply nth_error_None in H1.
      rewrite rev_map_spec in H1.
      rewrite rev_length in H1. rewrite map_length in H1.
      pose (H9 := lem8989 e na i H H0).
      lia.
  Qed.

  Lemma in_hd {A} (x:A) l :
    #|l| > 0 -> In (hd x l) l.
  Proof.
    induction l.
    + intros. simpl in H. inversion H.
    + intros. simpl. left. auto.
  Qed.

  Lemma lem_get_info_last {n k l ls} e na :
    eprop n k l ls e ->
    within_info l na 0 ->
    closedn n (get_info_last na e).
  Proof.
    intros.
    unfold get_info_last.
    pose proof (H' := lem_lookup_list e na H).
    pose proof (H1' := lem8989 e na 0 H H0).
    simpl.
    rewrite Forall_forall in H'.
    eapply H'.
    eapply in_hd. auto.
  Qed.

  Lemma lem_rel_of {n k l ls} e na :
    eprop n k l ls e ->
    within_info l na 0 ->
    closedn n (rel_of na e).
  Proof.
    eapply lem_geti_info.
  Qed.

End proof_geti_info.


Section proof_mapt.

  Lemma lem_geti_rename {n k l ls} e i:
    eprop n k l ls e ->
    i < k -> closedn n (geti_rename e i).
  Proof.
    intros.
    destruct H. destruct e. destruct ci0. simpl.
    clear Pl0. simpl in H1, H, ck0.
    unfold geti_rename. simpl.
    assert (In (nth i (map decl_type renaming) todo) (map decl_type renaming)).
    - eapply nth_In.
      rewrite (map_length decl_type). lia.
    - assert (forall x, In x (map decl_type renaming) -> closedn n x).
      + intros.
        simpl in H.
        eapply Forall_forall in H. 2: exact H3. destruct x. all:auto.
      + auto.
  Qed.

  Lemma lem_fold_right_update {n k l ls} e ctx:
    eprop n k l ls e ->
    eprop (n + #|ctx|) (k + #|ctx|) l ls
    (fold_right
      (fun na e => update_kp na e NoSave) e ctx).
  Proof.
    revert n k l e.
    induction ctx.
    + intros. simpl.
      assert (n + 0 = n); auto. assert (k + 0 = k);auto.
      rewrite H0, H1. auto.
    + intros.
      assert (n + #|a :: ctx| = S (n + #|ctx|)); auto.
      assert (k + #|a :: ctx| = S (k + #|ctx|)); auto.
      assert (l = replace_info_len NoSave l); auto.
      rewrite H0, H1, H2.
      change (
        eprop (S (n + #|ctx|)) (S (k + #|ctx|)) (replace_info_len NoSave l) ls
          (update_kp a (fold_right (fun na e0 => update_kp na e0 NoSave) e ctx) NoSave)
      ).
      eapply lem_update_kp.
      eapply IHctx.
      auto.
  Qed.

  Lemma lem_fold_left_update {n k l ls} e (defs:list (def term)):
    eprop n k l ls e ->
    eprop (n + #|defs|) (k + #|defs|) l ls
    (fold_left
      (fun e d => update_kp d.(dname) e NoSave) defs e).
  Proof.
    revert n k l e.
    induction defs.
    + intros. simpl.
      assert (n + 0 = n); auto. assert (k + 0 = k);auto.
      rewrite H0, H1. auto.
    + intros.
      assert (n + #|a :: defs| = S n + #|defs|). simpl. auto.
      assert (k + #|a :: defs| = S k + #|defs|). simpl. auto.
      assert (l = replace_info_len NoSave l); auto.
      rewrite H0, H1, H2.
      change (
        eprop (S n + #|defs|) (S k + #|defs|) (replace_info_len NoSave l) ls
         (fold_left (fun e d => update_kp d.(dname) e NoSave)
            defs (update_kp a.(dname) e NoSave))
      ).
      eapply IHdefs.
      eapply lem_update_kp.
      auto.
  Qed.

  Lemma lem_mapt {n k l ls} e t:
    eprop n k l ls e ->
    closedn k t ->
    closedn n (mapt e t).
  Proof.
    revert n k l e.
    induction t using term_forall_list_ind.
    + intros. simpl.
      eapply lem_geti_rename.
      exact H. simpl in H0. apply Compare_dec.leb_complete in H0. auto.
    + auto.
    + intros.
      simpl.
      apply forallb_Forall. apply Forall_map. apply Forall_forall.
      intros.
      rewrite Forall_forall in H.
      specialize (H x H2 _ _ _ _ H0).
      simpl in H1. apply forallb_Forall in H1. rewrite Forall_forall in H1.
      specialize (H1 x H2). auto.
    + auto.
    + intros.
      simpl. apply andb_and. simpl in H0. apply andb_and in H0. destruct H0.
      split. eapply IHt1. exact H. auto.
      eapply IHt2. exact H. auto.
    + intros. simpl in H0. apply andb_and in H0.
      destruct H0.
      change (closedn n0 (tProd n (mapt e t1) ((mapt (update_kp n e NoSave) t2)))).
      change (closedn n0 (mapt e t1) && (closedn (S n0) (mapt (update_kp n e NoSave) t2) )).
      apply andb_and. split.
      eapply IHt1. exact H. auto.
      eapply IHt2. 2:exact H1.
      eapply lem_update_kp. exact H.
    + intros. simpl in H0. apply andb_and in H0.
      destruct H0.
      change (closedn n0 (mapt e t1) && (closedn (S n0) (mapt (update_kp n e NoSave) t2) )).
      apply andb_and. split.
      eapply IHt1. exact H. auto.
      eapply IHt2. 2:exact H1.
      eapply lem_update_kp. exact H.
    + intros. simpl in H0. apply andb_and in H0.
      destruct H0. apply andb_and in H0. destruct H0.
      change (closedn n0 (mapt e t1) && closedn n0 (mapt e t2) && (closedn (S n0) (mapt (update_kp n e NoSave) t3) )).
      apply andb_and. split. apply andb_and. split.
      eapply IHt1. exact H. auto.
      eapply IHt2. exact H. auto.
      eapply IHt3.
      eapply lem_update_kp. exact H. auto.
    + intros. simpl in H1. apply andb_and in H1. destruct H1.
      simpl. apply andb_and. split.
      eapply IHt. exact H0. auto.
      apply forallb_Forall. apply Forall_map. apply Forall_forall.
      rewrite Forall_forall in H. intros. eapply H.
      auto. exact H0. apply forallb_Forall in H2. rewrite Forall_forall in H2. auto.
    + auto.
    + auto.
    + auto.
    + intros.
      simpl in H0. apply andb_and in H0. destruct H0.
      apply andb_and in H0. destruct H0.
      change (
        closedn n (
          tCase ci0
            (mk_predicate
              t.(puinst) (map (mapt e) t.(pparams)) t.(pcontext)
              (mapt (fold_right (fun na e => update_kp na e NoSave) e t.(pcontext)) t.(preturn))
              )
            (mapt e t0)
            (map (fun b => mk_branch b.(bcontext)
              (mapt (fold_right (fun na e => update_kp na e NoSave) e b.(bcontext)) b.(bbody)) ) l)
        )
      ).
      change (
        let p := mk_predicate
          t.(puinst) (map (mapt e) t.(pparams)) t.(pcontext)
          (mapt (fold_right (fun na e => update_kp na e NoSave) e t.(pcontext)) t.(preturn))
        in
        let c := (mapt e t0) in
        let brs := map (fun b => mk_branch b.(bcontext)
          (mapt (fold_right (fun na e => update_kp na e NoSave) e b.(bcontext)) b.(bbody)) ) l
        in
        let k := n in
        let k' := List.length (pcontext p) + k in
        let p' := test_predicate (fun _ => true) (closedn k) (closedn k') p in
        let brs' := test_branches_k closedn k brs in
        p' && closedn k c && brs'
      ).
      cbv zeta. apply andb_and. split. apply andb_and. split.
      unfold test_predicate in H0.
      apply andb_and in H0. destruct H0.
      apply andb_and in H0. destruct H0.
      apply forallb_Forall in H4.
      rewrite Forall_forall in H4.
      ++
        unfold tCasePredProp in X. destruct X.
        unfold test_predicate. apply andb_and. split.
        apply andb_and. split. auto. simpl.
        apply All_Forall in a. rewrite Forall_forall in a.
        apply forallb_Forall. apply Forall_map. apply Forall_forall.
        intros. eapply a. auto. 2:eapply H4. 2:auto. exact H.
        change (closedn (#|pcontext t| + n)
          (mapt
            (fold_right
              (fun (na : aname)
                  (e0 : infolocal) =>
                update_kp na e0 NoSave) e
              (pcontext t))
          (preturn t))
        ).
        eapply i.
        2: exact H3.
        assert (#|pcontext t| + n = n + #|pcontext t|). lia.
        assert (#|pcontext t| + k = k + #|pcontext t|). lia.
        rewrite H5, H6.
        eapply lem_fold_right_update. exact H.
      ++ eapply IHt. 2:exact H2. exact H.
      ++ apply forallb_Forall in H1.
        rewrite Forall_forall in H1.
        apply forallb_Forall. apply Forall_map.
        apply Forall_forall.
        intros.
        unfold tCaseBrsProp in X0.
        apply All_Forall in X0.
        rewrite Forall_forall in X0.
        unfold test_branch.
        change (
            closedn
              (#|bcontext x| + n)
              (mapt (fold_right
                          (fun (na : aname)
                            (e0 : infolocal) =>
                          update_kp na e0
                            NoSave) e
                          (bcontext x))
                      (bbody x)
              )
          ).
        assert (#|bcontext x| + k = k + #|bcontext x|). lia.
        assert (#|bcontext x| + n = n + #|bcontext x|). lia.
        rewrite H5.
        eapply (X0 _ _ (n + #|bcontext x|) (k + #|bcontext x|)). auto.
        specialize (H1 _ H3).
        unfold test_branch in H1. 2: rewrite <- H4.
        eapply lem_fold_right_update.
        exact H. auto. eapply H1. auto.
    + auto.
    + intros.
      simpl in H0. apply forallb_Forall in H0. rewrite Forall_forall in H0.
      unfold tFixProp in X. apply All_Forall in X.
      rewrite Forall_forall in X.
      change (closedn n0
        ( tFix
            (map
                (fun def =>
                    mkdef _
                      def.(dname)
                      (mapt e def.(dtype))
                      (mapt
                        (fold_left (fun e def => update_kp def.(dname) e NoSave) m e)
                      def.(dbody))
                      def.(rarg))
              m) n
        )
      ).
      change (
        let mfix :=
          (map
            (fun def =>
                mkdef _
                  def.(dname)
                  (mapt e def.(dtype))
                  (mapt
                    (fold_left (fun e def => update_kp def.(dname) e NoSave) m e)
                  def.(dbody))
                  def.(rarg))
          m) in
        let k := n0 in
        let k' := List.length mfix + k in
        List.forallb (test_def (closedn k) (closedn k')) mfix
      ).
      cbv zeta.
      apply forallb_Forall.
      apply Forall_map.
      apply Forall_forall.
      intros.
      unfold test_def. apply andb_and.
      specialize (H0 x H1). unfold test_def in H0. apply andb_and in H0. destruct H0.
      split.
      ++ simpl.
        eapply X. auto. exact H. auto.
      ++ rewrite map_length.
        change (closedn (#|m| + n0)
        (mapt
        (fold_left
            (fun
              (e0 : infolocal)
              (def :
                def term)
            =>
            update_kp
              (dname def)
              e0 NoSave) m
            e) (dbody x))
        ).
        eapply X. auto.
        assert (eq1: #|m| + n0 = n0 + #|m|). lia.
        rewrite eq1.
        eapply lem_fold_left_update.
        exact H.
        assert (eq2:#|m| + k = k + #|m|). lia.
        rewrite <- eq2.
        auto.
    + intros.
      simpl in H0. apply forallb_Forall in H0. rewrite Forall_forall in H0.
      unfold tFixProp in X. apply All_Forall in X.
      rewrite Forall_forall in X.
      change (closedn n0
        ( tFix
            (map
                (fun def =>
                    mkdef _
                      def.(dname)
                      (mapt e def.(dtype))
                      (mapt
                        (fold_left (fun e def => update_kp def.(dname) e NoSave) m e)
                      def.(dbody))
                      def.(rarg))
              m) n
        )
      ).
      change (
        let mfix :=
          (map
            (fun def =>
                mkdef _
                  def.(dname)
                  (mapt e def.(dtype))
                  (mapt
                    (fold_left (fun e def => update_kp def.(dname) e NoSave) m e)
                  def.(dbody))
                  def.(rarg))
          m) in
        let k := n0 in
        let k' := List.length mfix + k in
        List.forallb (test_def (closedn k) (closedn k')) mfix
      ).
      cbv zeta.
      apply forallb_Forall.
      apply Forall_map.
      apply Forall_forall.
      intros.
      unfold test_def. apply andb_and.
      specialize (H0 x H1). unfold test_def in H0. apply andb_and in H0. destruct H0.
      split.
      ++ simpl.
        eapply X. auto. exact H. auto.
      ++ rewrite map_length.
        change (closedn (#|m| + n0)
        (mapt
        (fold_left
            (fun
              (e0 : infolocal)
              (def :
                def term)
            =>
            update_kp
              (dname def)
              e0 NoSave) m
            e) (dbody x))
        ).
        eapply X. auto.
        assert (eq1: #|m| + n0 = n0 + #|m|). lia.
        rewrite eq1.
        eapply lem_fold_left_update.
        exact H.
        assert (eq2:#|m| + k = k + #|m|). lia.
        rewrite <- eq2.
        auto.
    + auto.
    + auto.
    + intros. simpl.
      simpl in H1. apply andb_and in H1. destruct H1.
      apply andb_and in H1. destruct H1.
      apply andb_and. split.
      apply andb_and. split.
      2: eapply IHt1. 2:exact H0. 2:auto.
      2: eapply IHt2. 2:exact H0. 2:auto.
      apply forallb_Forall. apply Forall_map. apply Forall_forall.
      intros. rewrite Forall_forall in H.
      eapply H. auto. exact H0. apply forallb_Forall in H1.
      rewrite Forall_forall in H1. auto.
      Unshelve. auto.
  Qed.

End proof_mapt.


(* specification of well-scoped inductive type *)
Section Is_closed.

  Inductive Is_closed_context : nat -> context -> Prop :=
    | closednil : forall n, Is_closed_context n []
    | closedcons (a:context_decl) (n:nat) (l:context):
        Is_closed_context n l -> closedn (n + #|l|) (decl_type a) ->
        Is_closed_context n (a :: l).

  Record Is_closed_constructor (n:nat) (ctor:constructor_body) : Prop :={
    is_closed_args : Is_closed_context n (cstr_args ctor);
    is_closed_cstr_type: closedn n (cstr_type ctor);
    is_closed_cstr_indices:
      Forall
        (fun index => closedn (n + #|ctor.(cstr_args)|) index)
          ctor.(cstr_indices)
  }.

  Record Is_closed_body (n:nat) (body:one_inductive_body) : Prop :={
    is_closed_indices : Is_closed_context n (ind_indices body);
    is_closed_constructors :
      Forall (fun ctor => Is_closed_constructor n ctor) (ind_ctors body);
    is_closed_ind_type: closedn n body.(ind_type)
  }.

  Record Is_closed_mutual_ind_body (ty:mutual_inductive_body) : Prop :={
    is_closed_params : Is_closed_context (#|ind_bodies ty|) (ind_params ty);
    is_closed_body:
      Forall
        (fun ind_body =>
          Is_closed_body (#|ind_bodies ty| + #|ind_params ty|) ind_body)
        (ind_bodies ty);
  }.

  Definition no_empty_bodies ty :=
    #|ty.(ind_bodies)| > 0.

End Is_closed.


Section proof_it_tProd.

  Lemma lem_within_replace {l str}:
    within_info (replace_add_l l str) str 0.
  Proof.
    induction l.
    + unfold within_info.
      unfold replace_add_l. simpl.
      assert (String.eqb str str = true). apply lemstr. auto.
      rewrite H. lia.
    + simpl. destruct a. simpl.
      destruct (String.eqb t str) eqn:e.
      ++ apply lemstr in e. rewrite e. simpl. auto.
        assert (String.eqb str str = true). apply lemstr. auto.
        unfold within_info. simpl. rewrite H. lia.
      ++ simpl.
        destruct (String.eqb str t) eqn:e1.
        -- apply lemstr in e1. rewrite e1 in e. assert (String.eqb t t = true). apply lemstr. auto.
            rewrite H in e. inversion e.
        -- simpl. unfold within_info. simpl. rewrite e1. auto.
  Qed.

  Lemma lemma_it_kptProd {n k l ls} e na params t2:
    eprop n k l ls e ->
    Is_closed_context k params ->
    (forall e0, eprop (n + #|params|) (k + #|params|) (addl l (Some na) #|params|) ls e0 -> closedn (n + #|params|) (t2 e0)) ->
    closedn n (it_kptProd_default (Some na) e params t2).
  Proof.
    intros. unfold it_kptProd_default.
    revert H1. revert t2. revert H0. revert params.
    induction params.
    + simpl. intros.
      simpl in H1.
      (* Search "add_0". *)
      assert (e1 : n + 0 = n). auto.
      assert (e2 : k + 0 = k). auto.
      rewrite e1, e2 in H1.
      eapply H1.
      destruct H.
      split.
      - destruct ci0. split.
        -- simpl. auto.
        -- destruct e. simpl. simpl in H2.
          constructor. auto. auto.
      - simpl. auto.
      - simpl. constructor. auto. auto.
      - auto.
    +
      intros.
      (* unfold it_kptProd_default. *)
      eapply IHparams.
      - inversion H0. auto.
      - intros. eapply lem_kptProd.

        -- exact H2.
        -- eapply lem_mapt. exact H2.
          inversion H0. auto.
        -- intros. simpl in H1.
          assert (S ( n + #|params|) = n + S #|params|).  auto.
          rewrite H4. apply H1.
          simpl in H3.
          assert (String.eqb na na = true). apply lemstr. auto.
          rewrite H5 in H3.
          rewrite <- H4.
          assert (S ( k + #|params|) = k + S #|params|).  auto.
          rewrite <- H6. auto.
  Qed.

  (* Definition it_mktProd_default' (saveinfo:option string) (e:infolocal) (ctx:context) (t: infolocal -> term) : term :=
    let e := add_emp_info e saveinfo in
    let saveinfo :=
      match saveinfo with | None => NoSave | Some str => Savelist str
    end in
    let fix Ffix ctx e e0 t:=
      match ctx with
      | [] => t e e0
      | decl :: ctx' =>
          Ffix ctx' e e0 (fun e e0 =>
            let e' := update_kp decl.(decl_name) e saveinfo in
            let e0 := update_mk decl.(decl_name) e0 saveinfo in
            tProd decl.(decl_name)
              (mapt e decl.(decl_type))
              (t e' e0)
          )
      end in
    Ffix ctx e e (fun _ => t). *)

  Lemma lemma_it_mktProd' {n k l ls} e na ctx t2:
    eprop n k l ls e ->
    Is_closed_context k ctx ->
    (forall e0' e0,
      eprop (n + #|ctx|) (k + #|ctx|) (addl l (Some na) #|ctx|) ls e0' ->
      eprop (n + #|ctx|) (k) (addl l (Some na) #|ctx|) ls e0 ->
      closedn (n + #|ctx|) (t2 e0' e0)
      ) ->
    closedn n (it_mktProd_default' (Some na) e ctx t2).
  Proof.
    intros. unfold it_mktProd_default'.
    revert H1. revert t2. revert H0. revert ctx.
    induction ctx.
    + simpl. intros.
      simpl in H1.
      assert (e1 : n + 0 = n). auto.
      rewrite e1 in H1.
      eapply H1.
      - destruct H.
        split.
        ++ destruct ci0. split.
          -- simpl. auto.
          -- destruct e. simpl. simpl in H2. auto.
        ++ simpl. lia.
        ++ simpl. constructor. auto. auto.
        ++ auto.
      - destruct H.
        split.
        ++ destruct ci0. split.
          -- simpl.  auto.
          -- destruct e. simpl in H2. simpl. auto.
        ++ simpl. auto.
        ++ simpl. constructor. auto. auto.
        ++ auto.
    +
      intros.
      eapply IHctx.
      - inversion H0. auto.
      - intros.
        change (closedn (n+#|ctx|) (mapt e0' (decl_type a)) &&
          closedn (S (n + #|ctx|)) (   (t2
          (update_kp
            (decl_name a)
            e0'
            (Savelist na))
          (update_mk
            (decl_name a)
            e0
            (Savelist na))))
        ).
        apply andb_and.
        split.
        -- eapply lem_mapt. exact H2. inversion H0. auto.
        -- simpl in H1.
          assert (H4 : S (n+#|ctx|) = n + S #|ctx|). auto. rewrite H4.
          assert (H8 : S (k+#|ctx|) = k + S #|ctx|). auto.
          assert (replace_info_len (Savelist na) ((na, #|ctx|)::l) = (na, S #|ctx|) :: l).
          unfold replace_info_len. unfold replace_add_l.
          assert (H999: String.eqb na na = true). apply lemstr. auto.
          rewrite H999. auto.
          eapply H1.
          ++ rewrite <- H5. rewrite <- H4. rewrite <- H8.
              eapply lem_update_kp. simpl in H2. auto.
          ++ rewrite <- H5. rewrite <- H4.
              eapply lem_update_mk. simpl in H2. auto.
  Qed.

  Lemma lemma_it_mktProd {n k l ls} e na ctx t2:
    eprop n k l ls e ->
    Is_closed_context k ctx ->
    (forall e0,
      eprop (n + #|ctx|) (k) (addl l (Some na) #|ctx|) ls e0 ->
      closedn (n + #|ctx|) (t2 e0)
      ) ->
    closedn n (it_mktProd_default (Some na) e ctx t2).
  Proof.
    unfold it_mktProd_default.
    intros.
    eapply lemma_it_mktProd'.
    exact H. auto. auto.
  Qed.

End proof_it_tProd.


Section proof_make_initial_info.

  Lemma in_mapi_rec {A B} (x:B) f k (l:list A) :
    In x (mapi_rec f l k) ->
      exists (i:nat), exists (a:A), i < #|l| + k  /\ x = f i a.
  Proof.
    revert k.
    induction l.
    - simpl. auto.
    - intro. intro H.
      inversion H.
      + exists k. exists a. split. simpl. lia.
        auto.
      + specialize (IHl (S k) H0).
        simpl.
        assert (#|l| + S k = S (#|l| + k)). lia.
        rewrite <- H1. auto.
  Qed.

  Lemma in_mapi {A B} (x:B) f (l:list A) :
    In x (mapi f l) ->
      exists (i:nat), exists (a:A), i < #|l|  /\ x = f i a.
  Proof.
    unfold mapi.
    assert (#|l| = #|l| + 0). auto. rewrite H.
    eapply in_mapi_rec.
  Qed.

  Lemma lem_initial : forall kn ty, Is_closed_mutual_ind_body ty ->
    eprop 0 #|ty.(ind_bodies)| [] [("rels_of_T", #|ty.(ind_bodies)|)] (make_initial_info kn ty).
  Proof.
    intros. destruct ty. simpl.
    destruct H as [H1 H2]. clear H1 H2.
    split.
    + split.
      ++ unfold make_initial_info. simpl.
        rewrite map_length.
        rewrite map_mapi. simpl.
        apply Forall_forall.
        intros.
        eapply in_mapi in H.
        destruct H. destruct H.
        rewrite map_length in H.
        destruct H.
        rewrite H0. auto.
      ++ unfold make_initial_info. simpl. auto.
    + unfold make_initial_info.
      simpl. rewrite mapi_length. rewrite map_length. auto.
    + auto.
    + unfold make_initial_info. simpl.
      constructor. split.
      ++ simpl. auto.
      ++ simpl. rewrite mapi_length. rewrite map_length. auto.
      ++ auto.
  Qed.

End proof_make_initial_info.

Section proof_is_rec_call.

  Lemma lemma_Ffix_findi l j i q:
    Ffix_findi l j i = Some q -> q < #|l| + j.
  Proof.
    revert j i q.
    induction l.
    + simpl. intros. inversion H.
    + intros. simpl.
      simpl in H.
      destruct (eqb a i).
      ++ inversion H. simpl. lia.
      ++ specialize (IHl _ _ _ H). lia.
  Qed.

  Lemma lem_is_rec_call {n k l ls} e i j:
    eprop n k l ls e ->
    is_rec_call e i = Some j ->
    within_info ls "rels_of_T" j.
  Proof.
    intros.
    (* Print is_rec_call. *)
    unfold is_rec_call in H0.
    eapply lemma_Ffix_findi in H0.
    rewrite rev_map_length in H0.
    destruct H as [_ _ _ Pls].
    induction Pls.
    + auto.
    + unfold within_info.
      destruct (String.eqb "rels_of_T" y.1) eqn:eq0.
      ++ unfold find. rewrite eq0. destruct H.
         destruct x.
         destruct y. simpl in H, H1.
          unfold lookup_list in H0.
          unfold find in H0.
          rewrite <- H in eq0.
          assert ((t, n0).1 = t). auto.
          rewrite H2 in eq0.
          rewrite eq0 in H0.
          lia.
      ++ unfold find. rewrite eq0.
          change (
            match
            (find
              (fun x0 => String.eqb "rels_of_T" x0.1)
              l')
            with
            | Some p =>
                let (_, n0) := p in j < n0
            | None => j < 0
            end
          ).
          destruct H. destruct x.
          unfold lookup_list in H0.
          unfold find in H0.
          rewrite <- H in eq0.
          assert ((t, l1).1 = t). auto.
          rewrite H2 in eq0.
          rewrite eq0 in H0.
          apply IHPls in H0.
          auto.
  Qed.

End proof_is_rec_call.
