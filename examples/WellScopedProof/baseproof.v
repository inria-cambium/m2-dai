Require Import MetaCoq.Programming.
Global Open Scope bs.
Import Lia.


(* Lemma lem1 {n} saveinfo e na t1 t2 :
  closedn n t1 ->
  (forall e0, closedn (S n) (t2 e0)) -> closedn n (mktProd saveinfo e na t1 t2).
Proof.
  intros.
  unfold mktProd. simpl.
  apply andb_and. auto.
Qed. *)



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
  (* apply Compare_dec.leb_correct. *)
  (* eapply Compare_dec.leb_complete in H2.  lia. *)
Qed.


Record eprop (n k:nat) (l:list (string * nat)) (e:infolocal) : Prop := mkeprop {
  ci : closed_info_n n e;
  ck : k <= #|e.(renaming)|;
  Pl : Forall2 (fun x y =>
    x.1 = y.1 /\ #|x.2| >= y.2
    ) e.(info) l;
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
  | None => l
  | Some str => replace_add_l l str
  end.



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



Lemma prop_update_mk {n k l} na e saveinfo :
  eprop n k l e -> eprop (S n) k (replace_info_len (Some saveinfo) l) (update_mk na e (Savelist saveinfo) ).
Proof.
  intros. destruct H.
  split.
  +
    destruct ci0.
    unfold update_mk. destruct e. simpl.
    unfold closed_info_n. split. simpl. simpl in H.
    - apply lem_renaming. auto.
    - simpl. simpl in H0. apply lem_info. auto.
  + simpl. rewrite <- lift_renaming_length. auto.
  + simpl. apply lemx01. auto.
Qed.

Lemma prop_update_kp {n k l} na e saveinfo :
  eprop n k l e -> eprop (S n) (S k) (replace_info_len (Some saveinfo) l) (update_kp na e (Savelist saveinfo) ).
Proof.
  intros. destruct H.
  split.
  +
    destruct ci0.
    unfold update_mk. destruct e. simpl.
    unfold closed_info_n. split. simpl. simpl in H.
    - constructor. auto. apply lem_renaming. auto.
    - simpl. simpl in H0. apply lem_info. auto.
  + simpl. rewrite <- lift_renaming_length. lia.
  + simpl. apply lemx01. auto.
Qed.


Lemma lem_mktProd {n k l} saveinfo e na t1 t2 :
  eprop n k l e ->
  closedn n t1 ->
  (forall e0, eprop (S n) k (replace_info_len (Some saveinfo) l) e0 -> closedn (S n) (t2 e0))
  -> closedn n (mktProd (Savelist saveinfo) e na t1 t2).
Proof.
  intros.
  unfold mktProd. unfold mktbind.
  pose (e1 := update_mk na e (Savelist saveinfo)).
  specialize (H1 e1).
  change (closedn n t1 && closedn (S n) (t2 e1)).
  apply andb_and. split. auto.
  apply H1. apply prop_update_mk. auto.
Qed.

Lemma lem_kptProd {n k l} saveinfo e na t1 t2 :
  eprop n k l e ->
  closedn n t1 ->
  (forall e0, eprop (S n) (S k) (replace_info_len (Some saveinfo) l) e0 -> closedn (S n) (t2 e0))
  -> closedn n (kptProd (Savelist saveinfo) e na t1 t2).
Proof.
  intros.
  unfold mktProd. unfold mktbind.
  pose (e1 := update_kp na e (Savelist saveinfo)).
  specialize (H1 e1).
  change (closedn n t1 && closedn (S n) (t2 e1)).
  apply andb_and. split. auto.
  apply H1. apply prop_update_kp. auto.
Qed.

Lemma lem_lookup_list {n k l} e (str:string)
  :
  eprop n k l e ->
  Forall (fun x => Nat.ltb (decl_type x) n) ((lookup_list (e.(info)) str)).
Proof.
  intro.
  destruct e.
  simpl. destruct H.
  destruct ci0. clear H. unfold lookup_list. simpl.
  destruct (find
  (fun
     i :
      string
      ×
      information =>
   let
     (na',
      _) :=
     i in
   String.eqb
     str na')
  info) eqn:eq0.
  - destruct p. simpl in H0.
    apply find_some in eq0.
    destruct eq0.
    rewrite Forall_forall in H0.
    pose (h0 := H0 (t, i) H). simpl in h0.
    rewrite Forall_map in h0. auto.
  - auto.
Qed.

Goal  In 3 [3].
  simpl. left. auto.
Qed.

(* Search "rev_map". *)

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
  (* rewrite rev_map_spec in H. *)
    (* rewrite <- in_rev in H. simpl in H. *)
    destruct H. + exists 0. exists a. auto.
    + auto.
Qed.

Lemma lem9975 n l
: In
(tRel n)
(map
   (fun
      x : 
       BasicAst.context_decl
       nat =>
    tRel
      (decl_type
       x))
   l)

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


Lemma lem_rels_of {n k l} e na:
  eprop n k l e ->
  Forall (fun t => closedn n t) (rels_of na e).
Proof.
  intro.
  pose (h0 := @lem_lookup_list n k l e na H).
  rewrite Forall_forall in h0.

  unfold rels_of. rewrite rev_map_spec.
  (* destruct e. simpl in h0. simpl. *)
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

Lemma lem8989 {n k l} e (str:string) (i:nat):
  eprop n k l e ->
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


Lemma lem_geti_info {n k l} e na i :
  eprop n k l e ->
  within_info l na i ->
  closedn n (geti_info na e i).
Proof.
  intros.
  (* destruct H. *)
  (* clear ck0. *)
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
  + (* rewrite e0 in H. *)
    eapply find_some in e0. destruct e0.
    destruct H.
    destruct ci0. simpl. simpl in H4.
    (* simpl in f0. *)
    assert (let '(_,l) := p in Forall
              (fun x : nat => PeanoNat.Nat.ltb x n)
              (map decl_type l)).
    ++
       rewrite Forall_forall in H4.
       exact (H4 p H2).
    ++
      destruct p.
      (* apply Forall_forall in H2. *)
      (* assert (forall x, In x l -> Nat.ltb (decl_type x) n). *)
      (* eapply Forall *)
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

Lemma lem_rel_of {n k l} e na :
  eprop n k l e ->
  within_info l na 0 ->
  closedn n (rel_of na e).
Proof.
  eapply lem_geti_info.
Qed.

Lemma lem_geti_rename {n k l} e i:
  eprop n k l e ->
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

(* Print term_ind. *)


(* Fixpoint mapt (e:infolocal) (t:term) : term:=
  match t with
  | tRel k => geti_rename e k
  | tEvar m tl => tEvar m (map (mapt e) tl)
  | tCast t1 ck t2 => tCast (mapt e t1) ck (mapt e t2)
  | tProd na t1 t2 => tProd na (mapt e t1) (mapt (update_kp na e NoSave) t2)
  | tLambda na t1 t2 => tLambda na (mapt e t1) (mapt (update_kp na e NoSave) t2)
  | tLetIn na t0 t1 t2 => tLetIn na (mapt e t0) (mapt e t1) (mapt (update_kp na e NoSave) t2)
  | tApp tx tl => tApp (mapt e tx) (map (mapt e) tl)
  | tProj pj t => 
  | tArray l arr t1 t2 => 
  | tCase ci p t0 bs => 
  | tFix mfix n => 
  | tCoFix mfix n => 
  | tVar _ | tSort _ | tConst _ _
  | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ => t end. *)

(* Require Import MetaCoq.PCUIC.Syntax.PCUICInduction.
About term_ind_size_app. *)

(* About term_ind. *)

Lemma lem_mapt {n k l} e t:
  eprop n k l e ->
  closedn k t ->
  closedn n (mapt e t).
Proof.
Admitted.


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

End Is_closed.

Definition addl (l:list (string*nat)) si i :=
  match si with
  | None => l
  | Some str => (str, i) :: l end.


Definition add_emp_info e saveinfo :=
  match saveinfo with
  | Some str =>
    mkinfo e.(renaming) ((str, []) :: e.(info)) e.(info_source) e.(kn)
  | _ => e end.

(* it_kptProd_default *)


Definition it_kptProd_default (saveinfo:option string) (e:infolocal) (ctx:context) (t: infolocal -> term) : term :=
  let e := add_emp_info e saveinfo in
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
          Ffix ctx' e (
            fun e =>
              kptProd saveinfo e decl.(decl_name)
                (mapt e decl.(decl_type)) t
          )
    end in
  Ffix ctx e t.


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


(* Goal forall {n k l}, forall e na,
  eprop n k l e ->
  closedn n (
  mktProd (Savelist "a") e na (
    tSort sProp
  ) (fun e => rel_of "a" e)).
Proof.
  intros.
  eapply lem_mktProd.
  exact H. auto. intros.
  eapply lem_rel_of.
  exact H0.
  simpl. eapply lem_within_replace.
Qed. *)



Lemma lemma_it_kptProd {n k l} e na params t2:
  eprop n k l e ->
  Is_closed_context k params ->
  (forall e0, eprop (n + #|params|) (k + #|params|) (addl l (Some na) #|params|) e0 -> closedn (n + #|params|) (t2 e0)) ->
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


Definition it_mktProd_default' (saveinfo:option string) (e:infolocal) (ctx:context)
  (t: infolocal -> infolocal -> term) : term :=
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
  Ffix ctx e e t.


Definition it_mktProd_default (saveinfo:option string) (e:infolocal) (ctx:context)
  (t: infolocal -> term) : term :=
  it_mktProd_default' saveinfo e ctx (fun _ => t).

Lemma lemma_it_mktProd' {n k l} e na ctx t2:
  eprop n k l e ->
  Is_closed_context k ctx ->
  (forall e0' e0,
    eprop (n + #|ctx|) (k + #|ctx|) (addl l (Some na) #|ctx|) e0' ->
    eprop (n + #|ctx|) (k) (addl l (Some na) #|ctx|) e0 ->
    closedn (n + #|ctx|) (t2 e0' e0)
    ) ->
  closedn n (it_mktProd_default' (Some na) e ctx t2).
Proof.
  intros. unfold it_mktProd_default'.
  revert H1. revert t2. revert H0. revert ctx.
  induction ctx.
  + simpl. intros.
    simpl in H1.
    (* Search "add_0". *)
    assert (e1 : n + 0 = n). auto.
    (* assert (e2 : k + 0 = k). auto. *)
    rewrite e1 in H1.
    eapply H1.
    - destruct H.
      split.
      ++ destruct ci0. split.
        -- simpl. auto.
        -- destruct e. simpl. simpl in H2. auto.
      ++ simpl. lia.
      ++ simpl. constructor. auto. auto.
    - destruct H.
      split.
      ++ destruct ci0. split.
        -- simpl.  auto.
        -- destruct e. simpl in H2. simpl. auto.
      ++ simpl. auto.
      ++ simpl. constructor. auto. auto.
  +
    intros.
    (* unfold it_kptProd_default. *)
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
         (* eapply H1. *)
         assert (replace_info_len (Some na) ((na, #|ctx|)::l) = (na, S #|ctx|) :: l).
         unfold replace_info_len. unfold replace_add_l.
         assert (H999: String.eqb na na = true). apply lemstr. auto.
         rewrite H999. auto.
         eapply H1.
         ++ rewrite <- H5. rewrite <- H4. rewrite <- H8.
            eapply prop_update_kp. simpl in H2. auto.
         ++ rewrite <- H5. rewrite <- H4.
            eapply prop_update_mk. simpl in H2. auto.
Qed.

Lemma lemma_it_mktProd {n k l} e na ctx t2:
  eprop n k l e ->
  Is_closed_context k ctx ->
  (forall e0,
    eprop (n + #|ctx|) (k) (addl l (Some na) #|ctx|) e0 ->
    closedn (n + #|ctx|) (t2 e0)
    ) ->
  closedn n (it_mktProd_default (Some na) e ctx t2).
Proof.
  unfold it_mktProd_default.
  intros.
  eapply lemma_it_mktProd'.
  exact H. auto. auto.
Qed.

(* Program Definition update_mk {n k nind:nat} {l} (na:aname) (e0:cinfo n k nind l)
  (saveinfo:option string) : cinfo (S n) k nind (replace_info_len saveinfo l):= *)














(* Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.


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
  . *)

(* Print mapi_rec. *)

Lemma in_mapi_rec {A B} (x:B) f k (l:list A) :
  In x (mapi_rec f l k) ->
    exists (i:nat), exists (a:A), i < #|l| + k  /\ x = f i a.
Proof.
  revert k.
  (* unfold mapi. *)
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
  eprop 0 #|ty.(ind_bodies)| [] (make_initial_info kn ty).
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
Qed.

Definition no_empty_bodies ty :=
  #|ty.(ind_bodies)| > 0.

Lemma in_hd {A} (x:A) l :
  #|l| > 0 ->
  In (hd x l) l.
Proof.
  induction l.
  + intros. simpl in H. inversion H.
  + intros. simpl. left. auto.
Qed.
