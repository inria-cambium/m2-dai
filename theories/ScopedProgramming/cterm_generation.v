Require Import MetaCoq.ScopedProgramming.cterm.
Require Import MetaCoq.ScopedProgramming.cinfo.
Require Import MetaCoq.ScopedProgramming.cbody.
(* Global Open Scope bs. *)

Import Lia.
Axiom todo : forall {A}, A.


Definition kpcProd {n k nind:nat} {l} (saveinfo:option string) na (e:cinfo n k nind l)
  (t1:cterm n) (t2 : cinfo (S n) (S k) nind (replace_info_len saveinfo l)-> cterm (S n)): cterm n:=
  let e' := update_kp na e saveinfo in
  cProd na (t1) (t2 e').

Definition mkcProd {n k nind:nat} {l} (saveinfo:option string) na (e:cinfo n k nind l)
  (t1:cterm n) (t2:cinfo (S n) k nind (replace_info_len saveinfo l) -> cterm (S n)) : cterm n:=
  let e' := update_mk na e saveinfo in
  cProd na t1 (t2 e').


Program Definition is_rec_call {n m nind l} (e:cinfo n m nind l) i :
  option ({i:nat | i < nind}) :=
  let e := ei e in
  let nrenaming := #|e.(renaming)| in
  (* let nind := e.(nind) in *)
  match Nat.ltb i nrenaming with
  | false => None
  | true => match Nat.leb (nrenaming - nind) i with
             | false => None
             | true => Some (existc (i - (nrenaming - nind))) end end.
Next Obligation.
  destruct e0. destruct ei. simpl. simpl in Heq_anonymous, Heq_anonymous0.
  apply eq_sym in Heq_anonymous.
  eapply Compare_dec.leb_complete in  Heq_anonymous.
  apply eq_sym in Heq_anonymous0.
  eapply Compare_dec.leb_complete in  Heq_anonymous0.
  lia.
Qed.

(* Print term. *)

Unset Guard Checking.
(*todo todo todo todo todo*)
Program Fixpoint Ffix_rename {n m nind:nat} {l} (e:cinfo n m nind l) (t:term) (h:closedn m t)
  {struct t}: cterm n :=
  match t with
  | tRel k =>  geti_rename e k _
  | tVar ident => cVar ident
  | tEvar m tl => cEvar m (map_In tl (fun t h' => Ffix_rename e t _))
  | tSort sort => cSort sort
  | tCast t1 ck t2 => cCast (Ffix_rename e t1 _) ck (Ffix_rename e t2 _)
  | tProd na t1 t2 =>
    cProd na
      (Ffix_rename  e t1 _)
      (Ffix_rename (update_kp na e None) t2 _)
  | tLambda na t1 t2 =>
    cLambda na
      (Ffix_rename e t1 _)
      (Ffix_rename (update_kp na e None) t2 _)
  | tLetIn na t0 t1 t2 =>
    cLetIn na (Ffix_rename e t0 _) (Ffix_rename e t1 _)
      (Ffix_rename (update_kp na e None) t2 _)
  | tApp tx tl =>
    cApp (Ffix_rename  e tx _)
      (map_In tl (fun t h' => Ffix_rename e t _ ))
  | tConst ind instance => cConst ind instance
  | tInd ind instance => cInd ind instance
  | tConstruct ind m instance => cConstruct ind m instance
  | tCase _ _ _ _ => exist _ t todo
  | tProj pj t => cProj pj (Ffix_rename e t _)
  | tFix _ _ | tCoFix _ _ => exist _ t todo
  | tInt i => cInt i
  | tFloat f => cFloat f
  | tArray l arr t1 t2 =>
    cArray l (map_In arr (fun t h' => Ffix_rename e t _))
      (Ffix_rename e t1 _) (Ffix_rename e t2 _)
  end.
Next Obligation. apply Compare_dec.leb_complete in h. auto. Qed.
Next Obligation. eapply forallb_Forall in h. eapply Forall_forall in h. 2:exact h'. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. apply andb_andI in H. destruct H. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. apply andb_andI in H. destruct H. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation. apply andb_andI in h. destruct h. auto. Qed.
Next Obligation.
  apply andb_andI in h. destruct h.
  eapply forallb_Forall in H0. eapply Forall_forall in H0. 2:exact h'. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h. apply andb_andI in H. destruct H.
  eapply forallb_Forall in H. eapply Forall_forall in H. 2:exact h'. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h. apply andb_andI in H. destruct H. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h. auto.
Qed.
(* Next Obligation. *)

Set Guard Checking.

Definition rename {n m nind:nat} {l} (e:cinfo n m nind l) (t:cterm m) : cterm n:=
  Ffix_rename e (proj1_sig t) (proj2_sig t).


Definition add_info_len (l:list (string*nat)) si i :=
  match si with
  | None => l
  | Some str => (str, i) :: l end.


Definition cast {k m:nat} : context_closed k m -> forall n:nat, m = n -> context_closed k n.
Proof.
  intros.
  rewrite <- H.
  exact X.
Defined.

Definition add_emp_info e saveinfo :=
  match saveinfo with
  | Some str =>
    mkinfo e.(renaming) ((str, []) :: e.(info)) e.(info_source) e.(kn)
  | _ => e end.

Program Fixpoint Ffix_kpcProd {n k m nind:nat} {l} (saveinfo:option string)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: forall (e:cinfo (n + m) (k+m) nind (add_info_len l saveinfo m)),
    cterm (n + m) ) {struct ctx}
  : cterm n :=
  (
    match ctx as ctx0 in context_closed _ m2
    return forall (a:m = m2), ((cast ctx m2 a) = ctx0) -> cterm n with
    | nnil => fun eq1 eq2 =>
        cterm_lift _ $ t (mkcinfo (add_emp_info (ei e) saveinfo) _ _ _)
    | ncons _ a ctx' =>
      fun eq1 eq2 =>
        Ffix_kpcProd saveinfo ctx' e
          (fun e' =>
            kpcProd saveinfo a.(decl_name) e'
              (rename e' (a.(decl_type)))
              (fun e'' => cterm_lift _ (t (mkcinfo (ei e'') _ _ _) )))
    end
  )  eq_refl eq_refl.
Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert (n = n + 0). lia. rewrite <- H.
  destruct saveinfo.
  - destruct ci. split. auto.
    simpl. destruct ei. simpl. constructor. auto.  simpl in H0. auto.
  - simpl. auto.
Qed.
Next Obligation. destruct e. simpl.
  destruct saveinfo. all:simpl. all:lia. Qed.
Next Obligation. destruct e. simpl. unfold add_info_len.
  destruct saveinfo.
  - simpl. constructor. auto. auto.
  - auto.
Qed.
Next Obligation. lia. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + n0) = n + S n0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. lia. Qed.
Next Obligation.
  destruct e''. simpl. destruct ei. simpl. simpl in Pl.  destruct saveinfo.
  + simpl in Pl. assert (String.eqb t0 t0  = true). apply lemstr. auto. rewrite H in Pl.
    simpl. auto.
  + auto.
Qed.
(* Next Obligation. *)


Program Definition it_kpcProd {n k m nind:nat} {l} (saveinfo:option string)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: forall (e:cinfo (n + m) (k + m) nind (add_info_len l saveinfo m)) ,
    cterm (n + m))
  : cterm n :=

  Ffix_kpcProd saveinfo ctx e t.
(* Next Obligation. destruct si. auto. auto. Qed. *)


Lemma lemy02 {l a b}: a < b ->
  Forall
    (fun x : nat =>
    PeanoNat.Nat.ltb x a)
    (map decl_type l)
  ->
  Forall
    (fun x0 : nat =>
    PeanoNat.Nat.ltb x0 b)
    (map decl_type
      (plus_one_index l)).
Proof.
  intros.
  induction l.
  - simpl. auto.
  - simpl. constructor. inversion H0.
    apply Compare_dec.leb_complete in H3. apply Compare_dec.leb_correct. lia.
    eapply IHl. inversion H0. auto.
Qed.

Lemma lemy03 {info a b}: a < b ->
  Forall
    (fun '(_, l) =>
    Forall
      (fun x : nat =>
        PeanoNat.Nat.ltb x
          a)
      (map decl_type l))
    info
  ->
  Forall
    (fun '(_, l1) =>
    Forall
      (fun x0 : nat =>
        PeanoNat.Nat.ltb x0 b)
      (map decl_type l1))
    (map
      (fun
          x0 : string
              × list
                  (BasicAst.context_decl
                    nat) =>
        (x0.1,
        plus_one_index x0.2))
      info).
Proof.
  intros.
  induction info.
  - auto.
  - simpl. inversion H0. constructor. destruct a0. simpl.
    eapply lemy02. 2: exact H3. lia. auto.
Qed.


Lemma lemx02 {renaming a b}: a < b ->
Forall
      (fun x : term =>
       match x with
       | tRel i =>
           PeanoNat.Nat.ltb i a
       | tInd _ _ => true
       | _ => false
       end)
      (map decl_type renaming)
->
Forall
  (fun x : term =>
   match x with
   | tRel i =>
       PeanoNat.Nat.ltb i b
   | tInd _ _ => true
   | _ => false
   end)
  (map decl_type
     (lift_renaming renaming)).
Proof.
  intros.
  induction renaming.
  - simpl. auto.
  - simpl. constructor.
    + inversion H0.
      destruct ((decl_type a0)). all: auto. simpl.
      apply Compare_dec.leb_complete in H3. apply Compare_dec.leb_correct. lia.
    + simpl. inversion H0. auto.
Qed.


Lemma lemx03 {info a b s na}: a < b ->
Forall
(fun '(_, l) =>
 Forall
   (fun x : nat =>
    PeanoNat.Nat.ltb x
      a)
   (map decl_type l))
info
->
Forall
  (fun '(_, l0) =>
   Forall
     (fun x : nat =>
      PeanoNat.Nat.ltb x
        b)
     (map decl_type l0))
  (replace_add_info
     (map
        (fun
           x : string
               × list
                   (BasicAst.context_decl
                   nat) =>
         (x.1,
          plus_one_index x.2))
        info) s
     (mkdecl na None 0)).
Proof.
  intros.
  assert  (0 < b). destruct a. auto. lia.
  induction info.
  - simpl.
    constructor. simpl. apply Forall_forall. intros. inversion H2. rewrite <- H3.
    apply Compare_dec.leb_correct. lia. inversion H3. auto.
  - simpl.
    destruct a0. simpl.
    destruct (String.eqb t s) eqn:e.
    + constructor. simpl. constructor. apply Compare_dec.leb_correct. auto.
      simpl in H0. inversion H0. eapply lemy02. 2: exact H4. lia.
      inversion H0. eapply lemy03. 2: exact H5. auto.
    + inversion H0. constructor. eapply lemy02. 2:exact H4. auto.
      auto.
Qed.

Lemma lemx04 {l a b}: a < b ->
  Forall
  (fun '(_, x) =>
  PeanoNat.Nat.ltb x a) l
  ->
  Forall
    (fun '(_, x) =>
      PeanoNat.Nat.ltb x b)
    (map
      (fun x : string × nat =>
        (x.1, S x.2)) l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl. inversion H0.
    constructor. destruct a0. simpl. apply Compare_dec.leb_complete in H3. apply Compare_dec.leb_correct. lia.
    simpl. apply IHl. auto.
Qed.


Definition add_info_len' l (s:string) (n:nat) :=
  (s, n) :: l.

Lemma mylem999 {info l na saveinfo n0} :
Forall2
(fun
   (x : string
        × list
           (BasicAst.context_decl
           nat))
   (y : string × nat)
 =>
 x.1 = y.1 /\
 #|x.2| = y.2) info
(add_info_len' l
   saveinfo n0)
->
Forall2
  (fun
     (x : string
          × list
              (BasicAst.context_decl
                 nat))
     (y : string × nat) =>
   x.1 = y.1 /\ #|x.2| = y.2)
  (replace_add_info
     (map
        (fun
           x : string
               × list
                   (BasicAst.context_decl
                   nat) =>
         (x.1,
          plus_one_index x.2))
        info) saveinfo
     (mkdecl na None 0))
  (add_info_len' l saveinfo
     (S n0))
.
Proof.
  intro.
  induction info.
  - inversion H.
  - simpl. destruct a. simpl.
    inversion H.
    simpl in H3. destruct H3.
    rewrite H3. assert (String.eqb saveinfo saveinfo = true). apply lemstr. auto.
    rewrite H7. constructor.
    simpl. split. auto. rewrite plus_one_index_length. auto.
    simpl. inversion H. eapply lemy01. exact H13.
Qed.

Program Fixpoint Ffix_mkcProd' {n k nind m:nat} {l} (saveinfo:string)
  (ctx:context_closed k m)
  (e:cinfo n k nind (add_info_len' l saveinfo 0))
  (e0:cinfo n k nind (add_info_len' l saveinfo 0))
  (t: cinfo (n + m) (k + m) nind (add_info_len' l saveinfo m) ->
      cinfo (n + m) k nind (add_info_len' l saveinfo m) -> cterm (n + m))
  {struct ctx}: cterm n :=
  (match ctx as ctx0 in context_closed _ m2
    return forall (a:m=m2), (cast ctx m2 a = ctx0) -> cterm n with
  | nnil => fun eq1 eq2 => cterm_lift _ $
    t (mkcinfo (ei e) _ _ _ )
      (mkcinfo (ei e0) _ _ _ )
  | ncons _ a ctx' => fun eq1 eq2 =>
    Ffix_mkcProd' saveinfo ctx' e e0
      (fun ea eb =>
      (* let ea' := update_kp a.(decl_name) ea saveinfo in *)
      (* let eb' := update_mk a.(decl_name) eb saveinfo in *)
        cProd a.(decl_name)
          (rename ea a.(decl_type))
          (cterm_lift _  $
            t
              (mkcinfo (ei (update_kp a.(decl_name) ea (Some saveinfo))) _ _ _)
              (mkcinfo (ei (update_mk a.(decl_name) eb (Some saveinfo))) _ _ _)
          ))
  end) eq_refl eq_refl.
Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e. simpl. lia. Qed.
Next Obligation. destruct e. simpl. auto. Qed.
Next Obligation. destruct e0. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e0. simpl. lia. Qed.
Next Obligation. destruct e0. simpl. auto. Qed.
Next Obligation. lia. Qed.
Next Obligation.
  simpl. destruct ea. simpl. split.
    + simpl. constructor. apply Compare_dec.leb_correct. lia.
      destruct ei, ci. simpl. simpl in H. eapply lemx02. 2: exact H. lia.
    + simpl. destruct ei, ci. simpl. simpl in H0. eapply lemx03. 2: exact H0. lia.
Qed.
Next Obligation.
  simpl. destruct ea. destruct ei. simpl. simpl in ck. rewrite <- lift_renaming_length. lia.
Qed.
Next Obligation.
  destruct ea. simpl. destruct ei. simpl. simpl in Pl. eapply mylem999. auto.
Qed.
Next Obligation.
  simpl. destruct eb. simpl. split.
  + simpl. destruct ei, ci. eapply lemx02. 2: exact H. lia.
  + simpl. destruct ei, ci. simpl. simpl in H0. eapply lemx03. 2: exact H0. lia.
Qed.
Next Obligation.
  simpl. destruct eb. destruct ei. simpl. simpl in ck. rewrite <- lift_renaming_length. lia.
Qed.
Next Obligation.
  destruct eb. simpl. destruct ei. simpl. simpl in Pl. eapply mylem999. auto.
Qed.

Program Definition add_emp_info' {n k nind l} (infon:cinfo n k nind l) s
  : cinfo n k nind (add_info_len' l s 0) :=
  let e := ei infon in
  mkcinfo
    (mkinfo e.(renaming) ((s, []) :: e.(info)) e.(info_source) e.(kn))
    _ _ _
    .
Next Obligation.
  destruct infon. simpl. split.
  + simpl. destruct ci. auto.
  + destruct ci. simpl. constructor. auto. auto.
Qed.
Next Obligation.
  destruct infon. simpl. auto.
Qed.
Next Obligation.
  simpl. constructor. auto. destruct infon. auto.
Qed.


Program Definition it_mkcProd {n k nind m:nat} {l} (saveinfo:string)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: cinfo (n + m) (k + m) nind (add_info_len' l saveinfo m)-> cterm (n + m)) : cterm n:=
  Ffix_mkcProd' saveinfo ctx
    (add_emp_info' e saveinfo)
    (add_emp_info' e saveinfo) (fun a _ => t a).

Lemma lem789 {A B}: forall (y:B) (l:list A) (f:nat->A->B),
  In y (mapi (fun i x => f i x) l) ->
    exists n:nat, exists x:A, y = f n x.
Proof.
  intros y l.
  induction l.
  - intros. simpl in H. auto.
  - intros. simpl in H.
    destruct H. + exists 0. exists a. auto.
    + unfold mapi in IHl.
      rewrite mapi_rec_Sk in H.
      eapply IHl in H.
      destruct H. destruct H.
      exists (S x). exists x0. auto.
Qed.


Program Definition make_initial_cinfo' (kn:kername)
  (ty:mutual_inductive_body_closed) :infolocal :=
  (mkinfo
    (mapi
      (fun i ind_body =>
        mkdecl
          {| binder_name := nNamed (ind_name' _ ind_body);
             binder_relevance := Relevant  |} None
          (tInd
            {| inductive_mind := kn;
              inductive_ind := ty.(nind') - i - 1 |}
            [])
          ) ty.(ind_bodies'))
    []
    [("rels_of_T", (mapi (fun i ind_body =>
      mkdecl  ({| binder_name := nNamed (ind_name' _ ind_body);
                    binder_relevance := Relevant  |}) None i
      ) ty.(ind_bodies')))]
    kn).

Program Definition make_initial_cinfo (kn:kername)
  (ty:mutual_inductive_body_closed)
  (h:wf_ind_closed ty)
  :cinfo 0 ty.(nind') ty.(nind') []
  :=
  mkcinfo (make_initial_cinfo' kn ty) _ _ _.
Next Obligation.
  unfold closed_info_n. firstorder. simpl.
  apply Forall_map.
  apply Forall_forall.
  intros.
  (* assert (e) *)
  eapply lem789 in H1. destruct H1. destruct H1.
  rewrite H1. simpl. auto.
Qed.
Next Obligation.
  rewrite mapi_length. destruct h. lia.
Qed.
(* Next Obligation. *)
