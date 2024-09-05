Require Import MetaCoq.ScopedProgramming.cterm.

Import Lia.


Record infolocal : Type := mkinfo {
  renaming : list (BasicAst.context_decl term);
  info : list (string * list (BasicAst.context_decl nat)) ;
  (* info_nat : list (string * nat); *)
  info_source : list (string * list (BasicAst.context_decl nat));
  kn : kername;
}.


Section index_manage.

  Definition plus_one_index (l: list (BasicAst.context_decl nat)) :=
    map (fun x => mkdecl x.(decl_name) x.(decl_body) (S x.(decl_type))) l.

  Definition plus_k_index (l: list (BasicAst.context_decl nat)) k :=
    map (fun x => mkdecl x.(decl_name) x.(decl_body) (x.(decl_type)+k)) l.

  Fixpoint replace_add_info (info:list (string * list (BasicAst.context_decl nat))) (na:string)
    (item : BasicAst.context_decl nat) :=
    match info with
    | [] => (na, [item]) :: []
    | (s, l0) :: info' =>
        if String.eqb s na then (s, (item::l0)) :: info'
        else (s, l0) :: (replace_add_info info' na item)
    end.

  Lemma plus_one_index_length {l} : #|plus_one_index l| = #|l|.
    induction l.
    + auto.
    + simpl. auto.
  Qed.

  Definition lift_tRel (t:term) :=
    match t with
    | tRel i => tRel (i+1)
    | _ => t end.

  Definition lift_renaming (l:list (BasicAst.context_decl term)) :=
    map (
      fun x => mkdecl x.(decl_name) x.(decl_body) (lift_tRel x.(decl_type))
    ) l.

  Definition lookup_list (e : infolocal) (na : string) : list (BasicAst.context_decl nat) :=
    let l := e.(info) in
    match find (fun i => match i with
                        | (na', _) => String.eqb na na'
                end) l  with
      Some (_,  l) => l
    | _ => []
    end.

  (* Definition lookup_item (e : infolocal) (na : string) : nat :=
    let l := e.(info_nat) in
    match find (fun i => match i with
    | (na', _) => String.eqb na na'
    end) l  with
    Some (_, n) => n
    | _ => todo (*todo error*)
    end. *)

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
      all: auto. simpl. apply Compare_dec.leb_correct. apply Compare_dec.leb_complete in H2.
      lia.
    + inversion H. auto.
  Qed.


  (* Lemma lem_info_nat {n:nat} info_nat0:
    Forall (fun '(_, x) => Nat.ltb x n) info_nat0
      ->
    Forall (fun '(_, x) => Nat.ltb x (S n))
    (map (fun x : string × nat => (x.1, S x.2)) info_nat0).
  Proof.
    induction info_nat0.
    - auto.
    - simpl. constructor. 2: eapply IHinfo_nat0. 2: eapply incl_Forall. 3: exact H. 2: firstorder.
      inversion H. destruct a. auto.
  Qed. *)

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




Definition closed_info_n (n:nat) (e:infolocal) :=
  Forall (fun x => match x with tRel i => Nat.ltb i n | tInd _ _ => true | _ => false end)
    (map decl_type e.(renaming))
  /\
  Forall (fun '(_, l) => Forall (fun x => Nat.ltb x n) (map decl_type l))
          e.(info)
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

Record cinfo (n k nind:nat) (l:list (string * nat)) :Type := mkcinfo {
  ei: infolocal;
  ci : closed_info_n n ei;
  ck : k <= #|ei.(renaming)|;
  Pl : Forall2 (fun x y => x.1 = y.1 /\ #|x.2| >= y.2) ei.(info) l;
}.

Arguments mkcinfo {n k nind l}.
Arguments ei {n k nind l}.


(* Inductive saveinfo:=
  | Savelist (s:string)
  | Saveitem (s:string)
  | NoSave. *)

Fixpoint replace_add_l (l:list (string * nat)) str :=
  match l with
  | [] => [(str, 1)]
  | (name, n) :: l' =>
    if String.eqb name str then (name, S n) :: l'
    else (name, n) :: (replace_add_l l' str)
  end.

Definition replace_info_len saveinfo (l:list (string * nat)) :=
  match saveinfo with
  | None => l
  | Some str => replace_add_l l str
  end.


Lemma lemstr: forall s1 s2 :string, String.eqb s1 s2 = true <-> s1 = s2.
  (* pose (h := bytestring.StringOT.compare_eq). *)
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


Program Definition update_kp {n} {k} {nind} {l} (na:aname) (e:cinfo n k nind l) (saveinfo:option string):
  cinfo (S n) (S k) nind (replace_info_len saveinfo l) :=
  let e := ei e in
  let item := mkdecl na None 0 in
  let item_mapt := mkdecl na None (tRel 0) in
  let renaming :=
    item_mapt ::
      (lift_renaming e.(renaming))
  in
  let info :=
    map (
      fun  x => (fst x, (plus_one_index (snd x)))
    ) e.(info)
  in
  let info_source :=
    map (
      fun  x => (fst x, (plus_one_index (snd x)))
    ) e.(info_source)
  in
  let e :=
    match saveinfo with
    | None => mkinfo renaming info info_source e.(kn)
    | Some str => mkinfo renaming (replace_add_info info str item) info_source e.(kn)
    end
  in
  @mkcinfo (S n) (S k) _ (replace_info_len saveinfo l)
    e _ _ _.
Obligation 1.
  destruct e0. destruct ei0. destruct ci0. simpl in f, f0.
  destruct saveinfo.
  - simpl. split.
    + simpl. constructor. auto.
      apply lem_renaming. auto.
    + simpl.
      eapply lem_info. auto.
  - simpl. split.
    + simpl. constructor. auto. apply lem_renaming. auto.
    + simpl. eapply lem_info0. auto.
Qed.
Next Obligation.
  destruct e0. destruct ei0. simpl. simpl in ck0.
  destruct saveinfo.
  - simpl. rewrite <- lift_renaming_length. lia.
  - simpl. rewrite <- lift_renaming_length. lia.
Qed.
Next Obligation.
  destruct e0. destruct ei0. simpl. simpl in Pl0.
  destruct saveinfo.
  - simpl. eapply lemx01. auto.
  - simpl. eapply lemy01. auto.
Qed.

Program Definition update_mk {n k nind:nat} {l} (na:aname) (e0:cinfo n k nind l)
  (saveinfo:option string) : cinfo (S n) k nind (replace_info_len saveinfo l):=
  let e := ei e0 in
  let info :=
    map (
      fun  x => (fst x, (plus_one_index (snd x)))
    ) e.(info)
  in
  (* let info_nat := map (
    fun x => (x.1, S x.2)
  ) e.(info_nat) in *)
  let renaming := lift_renaming e.(renaming) in
  let item := mkdecl na None 0 in
  let e := match saveinfo with
    | None => mkinfo renaming info e.(info_source) e.(kn)
    | Some str => mkinfo renaming (replace_add_info info str item) e.(info_source) e.(kn)    end
  in
  @mkcinfo (S n) k nind (replace_info_len saveinfo l)
    e _ _ _ .
Obligation 1.
  destruct saveinfo.
  - destruct e0.
    destruct ei0. destruct ci0. simpl in f, f0.
    simpl.
    split.
    + simpl.
      apply lem_renaming. auto.
    + simpl. eapply lem_info. auto.
  - destruct e0. destruct ei0. destruct ci0. simpl in f, f0.
    simpl. split.
    + simpl. auto. apply lem_renaming. auto.
    + simpl. eapply lem_info0. auto.
Qed.
Next Obligation.
  destruct saveinfo.
  - destruct e0. simpl. rewrite <- lift_renaming_length. lia.
  - destruct e0. simpl. rewrite <- lift_renaming_length. lia.
Qed.
Next Obligation.
  destruct e0. destruct ei0. simpl. simpl in Pl0.
  destruct saveinfo.
  - simpl. eapply lemx01. auto.
  - simpl. eapply lemy01. auto.
Qed.

(* Lemma lem_lookup_item {n k nind:nat} {l} (e:cinfo n k nind l) (str:string):
  lookup_item (ei e) str < n.
Proof.
  destruct e. simpl.
  destruct ci0. clear H. destruct H0. clear H. clear Pl0. clear ck0.
  destruct ei0.
  unfold lookup_item. simpl.
  destruct (find (fun i : string × nat => let (na', _) := i in String.eqb str na') info_nat0) eqn:eq0.
  - destruct p. simpl in H0.
    assert (In (t, n0) info_nat0). eapply find_some. exact eq0.
    (* simpl in H0. *)
    pose (p := (Forall_forall (fun '(_,x) => Nat.ltb x n)) info_nat0).
    destruct p.
    assert (Nat.ltb n0 n). clear H2.
    + firstorder.
    + firstorder.
      apply Compare_dec.leb_complete. auto.
  - apply todo. (*todo*)
Qed.


Program Definition rel_of {n k nind:nat} {l} (na:string) (e:cinfo n k nind l) : cterm n :=
  let k := lookup_item (ei e) na in
  existc (tRel k).
Obligation 1.
  apply Compare_dec.leb_correct.
  eapply lem_lookup_item.
Defined. *)


Program Definition geti_rename {n m nind:nat} {l} (e:cinfo n m nind l) (i:nat) (h:i<m) :cterm n :=
  let e' := ei e in
  let l := map decl_type e'.(renaming) in
  existc (nth i l todo).
Obligation 1.
  destruct e. destruct ei0. destruct ci0. simpl.
  simpl in ck0.
  assert (In (nth i (map decl_type renaming0) todo) (map decl_type renaming0)).
  - eapply nth_In.
    rewrite (map_length decl_type). lia.
  - assert (forall x, In x (map decl_type renaming0) -> closedn n x).
  + intros.
    simpl in f.
    eapply Forall_forall in f. 2: exact H0. destruct x. all:auto.
  + auto.
Qed.


Definition within_info l (str:string) (i:nat) :=
  match (find (fun x => String.eqb str x.1) l) with
  | Some (_, n) => i < n
  | None => i < 0 end.


Definition has_info (l:list (string*nat)) str i :=
  match
    (find (fun x => String.eqb str x.1) l) with
  | Some (_, k) => i <= k
  | None => False
  end.

Lemma lem8989 {n k nind l} (e:cinfo n k nind l) (str:string) (i:nat):
  within_info l str i -> i < #|lookup_list (ei e) str|.
Proof.
  intro.
  destruct e. simpl. unfold within_info in H.
  unfold lookup_list. destruct ei0. simpl.
  simpl in Pl0. simpl in H.
  clear ck0. clear ci0.
  induction Pl0.
  - auto.
  - destruct x, y. simpl in H0.
    simpl. simpl in H.
    destruct H0. rewrite H0.
    destruct (String.eqb str t0) eqn:e0.
    + lia.
    + auto.
Qed.


Program Definition geti_info {n k nind l} (na:string) (e:cinfo n k nind l) (i:nat)
  (h:within_info l na i) :cterm n :=
  let l := rev (lookup_list (ei e) na) in
  match nth_error l i with
  | Some x => existc (tRel (decl_type x))
  | None => todo end.
Next Obligation.
  assert (nth_error
          (rev (lookup_list (ei e) na))
          i = Some x). auto.
  eapply nth_error_In in H.
  unfold lookup_list in H. destruct e. destruct ei0. simpl in H.
  destruct (find  (fun
              i : string
                  × list
                      (BasicAst.context_decl nat)
            =>
            let (na', _) := i in
            String.eqb na na') info0 ) eqn:e0.
  + eapply find_some in e0. destruct e0.
    destruct ci0.
    simpl in f0.
    assert (let '(_,l) := p in Forall
              (fun x : nat => PeanoNat.Nat.ltb x n)
              (map decl_type l)).
    ++ clear h  Heq_anonymous.
       rewrite Forall_forall in f0.
       exact (f0 p  H0).
    ++
      destruct p.
      (* apply Forall_forall in H2. *)
      assert (forall x, In x l -> Nat.ltb (decl_type x) n).
      (* eapply Forall *)
      rewrite Forall_forall in H2.
      intro x0. intro.
      assert (In (decl_type x0) (map decl_type l)).
      eapply in_map. auto.
      eapply H2 in H4. auto. eapply H3. eapply In_rev. auto.
  + inversion H.
Qed.

Program Definition get_info_last {n k nind l} (na:string) (e:cinfo n k nind l)
  (h:within_info l na 0) :cterm n :=
  let l := (lookup_list (ei e) na) in
  match nth_error l 0 with
  | Some x => existc (tRel (decl_type x))
  | None => todo end.
Next Obligation.
  assert (nth_error
          ( (lookup_list (ei e) na))
          0 = Some x). auto.
  eapply nth_error_In in H.
  unfold lookup_list in H. destruct e. destruct ei0. simpl in H.
  destruct (find  (fun
              i : string
                  × list
                      (BasicAst.context_decl nat)
            =>
            let (na', _) := i in
            String.eqb na na') info0 ) eqn:e0.
  + eapply find_some in e0. destruct e0.
    destruct ci0.
    simpl in f0.
    assert (let '(_,l) := p in Forall
              (fun x : nat => PeanoNat.Nat.ltb x n)
              (map decl_type l)).
    ++ clear h  Heq_anonymous.
       rewrite Forall_forall in f0.
       exact (f0 p  H0).
    ++
      destruct p.
      (* apply Forall_forall in H2. *)
      assert (forall x, In x l -> Nat.ltb (decl_type x) n).
      (* eapply Forall *)
      rewrite Forall_forall in H2.
      intro x0. intro.
      assert (In (decl_type x0) (map decl_type l)).
      eapply in_map. auto.
      eapply H2 in H4. auto. auto.
  + inversion H.
Qed.




Program Definition rel_of {n k nind:nat} {l} (na:string) (e:cinfo n k nind l)
  (h:within_info l na 0) : cterm n :=
  geti_info na e 0 h.

Lemma lem_lookup_list {n k nind:nat} {l} (e:cinfo n k nind l) (str:string):
  Forall (fun x => Nat.ltb  (decl_type x) n) ((lookup_list (ei e) str)).
Proof.
  destruct e. destruct ei0.
  simpl.
  destruct ci0. clear H. unfold lookup_list. simpl.
  destruct (find
  (fun
     i :
      string
      ×
      list
      (BasicAst.context_decl
      nat) =>
   let
     (na',
      _) :=
     i in
   String.eqb
     str na')
  info0) eqn:eq0.
  - destruct p. simpl in H0.
    apply find_some in eq0.
    destruct eq0.
    rewrite Forall_forall in H0.
    pose (h0 := H0 (t,l0) H). simpl in h0.
    rewrite Forall_map in h0. auto.
  - auto.
Qed.

Program Definition rels_of {n k nind:nat} {l} (na:string) (e:cinfo n k nind l): list (cterm n):=
  rev (map_In (lookup_list (ei e) na)
    (fun x xinl => exist _ (tRel (decl_type x)) _)).
Next Obligation.
  pose (h0 := lem_lookup_list e na).
  rewrite Forall_forall in h0.
  pose proof (h0 x xinl). auto.
Qed.

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

Lemma lem_app_closed {t tl n} : closedn n (tApp t tl) -> forall t', In t' tl -> closedn n t'.
Proof.
  intros.
  simpl in H. apply andb_andI in H. destruct H.
  apply forallb_Forall in H1.
  eapply Forall_forall in H1. 2:exact H0. auto.
Qed.