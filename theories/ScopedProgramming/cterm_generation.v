Require Import MetaCoq.ScopedProgramming.cterm.
Require Import MetaCoq.ScopedProgramming.cinfo.
Require Import MetaCoq.ScopedProgramming.cbody.
(* Global Open Scope bs. *)

Import Lia.
Axiom todo : forall {A}, A.


Definition kpcProd {n k l ls} (saveinfo:option string) na (e:cinfo n k l ls)
  (t1:cterm n) (t2 : cinfo (S n) (S k) (replace_info_len saveinfo l) ls-> cterm (S n)): cterm n:=
  let e' := update_kp na e saveinfo in
  cProd na (t1) (t2 e').

Definition mkcProd {n k l ls} (saveinfo:option string) na (e:cinfo n k l ls)
  (t1:cterm n) (t2:cinfo (S n) k (replace_info_len saveinfo l) ls -> cterm (S n)) : cterm n:=
  let e' := update_mk na e saveinfo in
  cProd na t1 (t2 e').


Fixpoint Ffix_findi (l:list nat) (j:nat) (i:nat) :=
  match l with
  | k :: l0 => if eqb k i then Some j else Ffix_findi l0 (j+1) i
  | [] => None
  end.

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
(* Definition is_rec_call (e:infolocal) i : 
  option nat:=
  let l := rev_map (fun x => x.(decl_type)) (lookup_list e.(info_source) "rels_of_T") in
  Ffix_findi l 0 i. *)

Program Definition is_rec_call {n m l ls} (e:cinfo n m l ls) i :
  option ({i:nat | within_info ls "rels_of_T" i}) :=
  let e := ei e in
  let l := rev_map (fun x => x.(decl_type)) (lookup_list e.(info_source) "rels_of_T") in
  match Ffix_findi l 0 i with
  | None => None
  | Some k => Some (existc k) end.
Next Obligation.
  symmetry in Heq_anonymous.
  eapply lemma_Ffix_findi in Heq_anonymous.
  rewrite rev_map_length in Heq_anonymous.
  destruct e0. destruct ei. simpl in Heq_anonymous.
  clear ci ck Pl.
  simpl in Pls.
  induction Pls.
  + simpl in Heq_anonymous. inversion Heq_anonymous.
  + unfold within_info. unfold find.
    unfold lookup_list in Heq_anonymous.
    unfold find in Heq_anonymous.
    destruct (String.eqb "rels_of_T" y.1) eqn:eq0.
    - destruct x, y. simpl in H. destruct H.
      eapply lemstr in eq0. simpl in eq0.
      rewrite eq0 in Heq_anonymous.
      rewrite H in Heq_anonymous.
      assert (String.eqb t0 t0 = true). eapply lemstr. auto.
      rewrite H1 in Heq_anonymous.
      rewrite H0 in Heq_anonymous. lia.
    - destruct x, y. simpl in H. destruct H.
      rewrite <- H in eq0.
      unfold ".1" in eq0. rewrite eq0 in Heq_anonymous.
      eapply IHPls. auto.
Qed.


Program Fixpoint it_update_kp {n k l ls} names (e:cinfo n k l ls): (cinfo (#|names| + n ) (#|names| + k) _ _) :=
  match names with
  | [ ] => e
  | na :: names => it_update_kp names (update_kp na e None) end.
(* Next Obligation. *)
Program Fixpoint it_update_kp_defs {n k nind l} (defs:list (def term)) (e:cinfo n k nind l): (cinfo (#|defs| + n ) (#|defs| + k) _ _) :=
  match defs with
  | [] => e
  | def :: defs' => it_update_kp_defs defs' (update_kp def.(dname) e None) end.
(* Next Obligation. *)

Unset Guard Checking.

Program Fixpoint Ffix_mapt {n m l ls} (e:cinfo n m l ls) (t:term) (h:closedn m t)
  {struct t}: cterm n :=
  match t with
  | tRel k =>  geti_rename e k _
  | tVar ident => cVar ident
  | tEvar m tl => cEvar m (map_In tl (fun t h' => Ffix_mapt e t _))
  | tSort sort => cSort sort
  | tCast t1 ck t2 => cCast (Ffix_mapt e t1 _) ck (Ffix_mapt e t2 _)
  | tProd na t1 t2 =>
    cProd na
      (Ffix_mapt  e t1 _)
      (Ffix_mapt (update_kp na e None) t2 _)
  | tLambda na t1 t2 =>
    cLambda na
      (Ffix_mapt e t1 _)
      (Ffix_mapt (update_kp na e None) t2 _)
  | tLetIn na t0 t1 t2 =>
    cLetIn na (Ffix_mapt e t0 _) (Ffix_mapt e t1 _)
      (Ffix_mapt (update_kp na e None) t2 _)
  | tApp tx tl =>
    cApp (Ffix_mapt e tx _)
      (map_In tl (fun t h' => Ffix_mapt e t _ ))
  | tConst ind instance => cConst ind instance
  | tInd ind instance => cInd ind instance
  | tConstruct ind m instance => cConstruct ind m instance
  | tCase ci p t0 bl =>
    cCase ci
      {|cpunist := p.(puinst);
        cpparms := map_In p.(pparams) (fun t h' => Ffix_mapt e t _);
        cpcontext := p.(pcontext);
        cpreturn := Ffix_mapt (it_update_kp p.(pcontext) e) p.(preturn) _;
      |}
      (Ffix_mapt e t0 _)
      (map_In bl
        (fun b h' =>
          {|
            cbcontext := b.(bcontext);
            cbbody := Ffix_mapt (it_update_kp b.(bcontext) e) b.(bbody) _
          |}
        ))
  | tProj pj t => cProj pj (Ffix_mapt e t _)
  | tFix mfix k =>
      let e' := (it_update_kp_defs mfix e) in
      cFix (
        existc (map_In mfix (fun def h' => {|
                  cdname := def.(dname);
                  cdtype := Ffix_mapt e def.(dtype) _;
                  cdbody := Ffix_mapt e' def.(dbody) _;
                  crarg := def.(rarg)
                |}))
      ) k
  | tCoFix mfix k =>
      let e' := (it_update_kp_defs mfix e) in
      cCoFix (
        existc (map_In mfix (fun def h' => {|
                  cdname := def.(dname);
                  cdtype := Ffix_mapt e def.(dtype) _;
                  cdbody := Ffix_mapt e' def.(dbody) _;
                  crarg := def.(rarg)
                |}))
      ) k
  | tInt i => cInt i
  | tFloat f => cFloat f
  | tArray l arr t1 t2 =>
    cArray l (map_In arr (fun t h' => Ffix_mapt e t _))
      (Ffix_mapt e t1 _) (Ffix_mapt e t2 _)
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
  apply andb_andI in h. destruct h.
  apply andb_andI in H. destruct H.
  unfold test_predicate in H. simpl in H. apply andb_andI in H. destruct H.
  apply forallb_Forall in H.
  eapply (Forall_forall) in H.
  2:exact h'. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h.
  apply andb_andI in H. destruct H.
  unfold test_predicate in H. simpl in H. apply andb_andI in H. destruct H. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h.
  apply andb_andI in H. destruct H. auto.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h. clear H.
  apply forallb_Forall in H0.
  assert (test_branch (closedn
            (#|bcontext b| + m)) b).
  eapply Forall_forall in H0. 2:exact h'. auto.
  unfold test_branch in H. auto.
Qed.
Next Obligation.
  apply forallb_Forall in h.
  eapply Forall_forall in h. 2:exact h'.
  unfold test_def in h. apply andb_andI in h. destruct h. auto.
Qed.
Next Obligation.
  apply forallb_Forall in h.
  eapply Forall_forall in h. 2:exact h'.
  unfold test_def in h. apply andb_andI in h. destruct h. auto.
Qed.
Next Obligation.
  rewrite <- map_In_length. auto.
Qed.
Next Obligation.
  apply forallb_Forall in h.
  eapply Forall_forall in h. 2:exact h'.
  unfold test_def in h. apply andb_andI in h. destruct h. auto.
Qed.
Next Obligation.
  apply forallb_Forall in h.
  eapply Forall_forall in h. 2:exact h'.
  unfold test_def in h. apply andb_andI in h. destruct h. auto.
Qed.
Next Obligation.
  rewrite <- map_In_length. auto.
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

Definition mapt {n m l ls} (e:cinfo n m l ls) (t:cterm m) : cterm n:=
  Ffix_mapt e (proj1_sig t) (proj2_sig t).


Definition addl (l:list (string*nat)) si i :=
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

Program Fixpoint Ffix_kpcProd {n k m l ls} (saveinfo:option string)
  (ctx:context_closed k m) (e:cinfo n k l ls)
  (t: cinfo (n + m) (k+m) (addl l saveinfo m) ls -> cterm (n + m) ) {struct ctx}
  : cterm n :=
  (
    match ctx as ctx0 in context_closed _ m2
    return forall (a:m = m2), ((cast ctx m2 a) = ctx0) -> cterm n with
    | nnil => fun eq1 eq2 =>
        cterm_lift _ $ t (mkcinfo (add_emp_info (ei e) saveinfo) _ _ _ _)
    | ncons _ a ctx' =>
      fun eq1 eq2 =>
        Ffix_kpcProd saveinfo ctx' e
          (fun e' =>
            kpcProd saveinfo a.(decl_name) e'
              (mapt e' (a.(decl_type)))
              (fun e'' => cterm_lift _ (t (mkcinfo (ei e'') _ _ _ _) )))
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
Next Obligation. destruct e. simpl. unfold addl.
  destruct saveinfo.
  - simpl. constructor. auto. auto.
  - auto.
Qed.
Next Obligation. destruct e. destruct ei. unfold add_emp_info. simpl. destruct saveinfo. auto. auto. Qed.
Next Obligation. lia. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + n0) = n + S n0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. lia. Qed.
Next Obligation.
  destruct e''. simpl. destruct ei. simpl. simpl in Pl.  destruct saveinfo.
  + simpl in Pl. assert (String.eqb t0 t0  = true). apply lemstr. auto. rewrite H in Pl.
    simpl. auto.
  + auto.
Qed.
Next Obligation. destruct e''. destruct ei. unfold add_emp_info. simpl. destruct saveinfo. auto. auto. Qed.
(* Next Obligation. *)

Program Definition it_kpcProd {n k m l ls} (saveinfo:option string)
  (ctx:context_closed k m) (e:cinfo n k l ls)
  (t: forall (e:cinfo (n + m) (k + m) (addl l saveinfo m) ls) ,
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


Definition addl' l (s:string) (n:nat) :=
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
(addl' l
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
  (addl' l saveinfo
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
    simpl. inversion H. eapply lemy01. auto.
Qed.

Program Fixpoint Ffix_mkcProd' {n k l ls} {m} (saveinfo:string)
  (ctx:context_closed k m)
  (e:cinfo n k (addl' l saveinfo 0) ls)
  (e0:cinfo n k (addl' l saveinfo 0) ls)
  (t: cinfo (n + m) (k + m) (addl' l saveinfo m) ls ->
      cinfo (n + m) k (addl' l saveinfo m) ls -> cterm (n + m))
  {struct ctx}: cterm n :=
  (match ctx as ctx0 in context_closed _ m2
    return forall (a:m=m2), (cast ctx m2 a = ctx0) -> cterm n with
  | nnil => fun eq1 eq2 => cterm_lift _ $
    t (mkcinfo (ei e) _ _ _ _ )
      (mkcinfo (ei e0) _ _ _ _ )
  | ncons _ a ctx' => fun eq1 eq2 =>
    Ffix_mkcProd' saveinfo ctx' e e0
      (fun ea eb =>
        cProd a.(decl_name)
          (mapt ea a.(decl_type))
          (cterm_lift _  $
            t
              (mkcinfo (ei (update_kp a.(decl_name) ea (Some saveinfo))) _ _ _ _)
              (mkcinfo (ei (update_mk a.(decl_name) eb (Some saveinfo))) _ _ _ _)
          ))
  end) eq_refl eq_refl.
Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e. simpl. lia. Qed.
Next Obligation. destruct e. simpl. auto. Qed.
Next Obligation. destruct e. simpl. auto. Qed.

Next Obligation. destruct e0. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e0. simpl. lia. Qed.
Next Obligation. destruct e0. simpl. auto. Qed.
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
  destruct ea. simpl. destruct ei. simpl. auto. eapply lemy01. auto. Qed.
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
Next Obligation.
destruct eb. simpl. destruct ei. simpl. auto. Qed.
(* Next Obligation. *)


Program Definition add_emp_info' {n k l ls} (infon:cinfo n k l ls) s
  : cinfo n k (addl' l s 0) ls:=
  let e := ei infon in
  mkcinfo
    (mkinfo e.(renaming) ((s, []) :: e.(info)) e.(info_source) e.(kn))
    _ _ _ _
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
Next Obligation. destruct infon. auto. Qed.


Program Definition it_mkcProd {n k l ls} {m} (saveinfo:string)
  (ctx:context_closed k m) (e:cinfo n k l ls)
  (t: cinfo (n + m) (k + m) (addl' l saveinfo m) ls -> cterm (n + m)) : cterm n:=
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
  :cinfo 0 ty.(nind') [] [("rels_of_T", ty.(nind'))]
  :=
  mkcinfo (make_initial_cinfo' kn ty) _ _ _ _.
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
Next Obligation.
  constructor. 2:auto.
  simpl. split. auto.
  rewrite mapi_length. destruct h. auto.
Qed.
