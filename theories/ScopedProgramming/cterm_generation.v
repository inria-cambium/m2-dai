Require Import MetaCoq.ScopedProgramming.cterm.
Require Import MetaCoq.ScopedProgramming.cinfo.
Require Import MetaCoq.ScopedProgramming.cbody.
(* Global Open Scope bs. *)

Import Lia.
Axiom todo : forall {A}, A.


Definition kpcProd {n k nind:nat} {l} (saveinfo:saveinfo) na (e:cinfo n k nind l)
  (t1:cterm n) (t2 : cinfo (S n) (S k) nind (replace_info_len saveinfo l)-> cterm (S n)): cterm n:=
  let e' := update_kp na e saveinfo in
  cProd na (t1) (t2 e').

Definition mkcProd {n k nind:nat} {l} (saveinfo:saveinfo) na (e:cinfo n k nind l)
  (t1:cterm n) (t2:cinfo (S n) k nind (replace_info_len saveinfo l) -> cterm (S n)) : cterm n:=
  let e' := update_mk na e saveinfo in
  cProd na t1 (t2 e').


Program Definition is_recursive_call_gen {n m nind l} (e:cinfo n m nind l) i :
  option ({i:nat | i < nind}) :=
  let e := ei n m _ l e in
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


Unset Guard Checking.

Program Fixpoint Ffix_type_rename {n m nind:nat} {l} (e:cinfo n m nind l) (t:term) (h:closedn m t)
  {struct t}: cterm n :=
  (match t as t0 return t = t0 -> cterm n with
  | tRel k => fun eq => geti_rename e k _
  | tApp tx tl => fun eq =>
      cApp (Ffix_type_rename  e tx _)
        (map_In tl (fun t h' => Ffix_type_rename e t _ ))
  | tProd na t1 t2 => fun eq =>
    cProd na
      (Ffix_type_rename  e t1 _)
      (Ffix_type_rename (update_kp na e NoSave) t2 _)
  | _ => fun eq => exist _ t todo(* todo *)
  end) eq_refl.
Next Obligation.
  apply Compare_dec.leb_complete in h. lia.
Qed.
Next Obligation.
  apply andb_andI in h. destruct h. auto.
Qed.
(* Next Obligation. lia. Qed. *)
Next Obligation.
apply andb_andI in h. destruct h. auto.
Qed.
(* Next Obligation.  lia. Qed. *)
Next Obligation.
apply andb_andI in h. destruct h. auto.
Qed.
(* Next Obligation. lia. Qed. *)
Next Obligation.
  apply andb_andI in h. destruct h.
  eapply forallb_Forall in H0. eapply Forall_forall in H0. 2:exact h'. auto.
Qed.
(* Next Obligation. *)
Set Guard Checking.

Definition type_rename_transformer {n m nind:nat} {l} (e:cinfo n m nind l) (t:cterm m) : cterm n:=
  Ffix_type_rename e (proj1_sig t) (proj2_sig t).

(* Definition add_info_len' (l:list (string*nat)) si i :=
  (* if eqb i 0 then l else *)
  match si with
  | None => l
  | Some str => (str, i) :: l end. *)

Definition add_info_len (l:list (string*nat)) si i :=
  (* if eqb i 0 then l else *)
  match si with
  | NoSave => l
  | Saveitem _ => l
  | Savelist str => (str, i) :: l end.


(* Require Import MetaCoq.ScopedProgramming.cbody. *)

Definition cast {k m:nat} : context_closed k m -> forall n:nat, m = n -> context_closed k n.
Proof.
  intros.
  rewrite <- H.
  exact X.
Defined.

Definition add_emp_info e saveinfo :=
  match saveinfo with
  | Savelist str =>
    mkinfo e.(renaming) ((str, []) :: e.(info)) e.(info_nat) e.(info_source) e.(kn)
  | _ => e end.

Program Fixpoint Ffix_kpcProd {n k m nind:nat} {l} (saveinfo:saveinfo)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: forall (e:cinfo (n + m) (k+m) nind (add_info_len l saveinfo m)),
    cterm (n + m) ) {struct ctx}
  : cterm n :=
  (
    match ctx as ctx0 in context_closed _ m2
    return forall (a:m = m2), ((cast ctx m2 a) = ctx0) -> cterm n with
    | nnil => fun eq1 eq2 =>
        cterm_lift _ $ t (mkcinfo _ _ _ _ (add_emp_info (ei _ _ _ _ e) saveinfo) _ _ _)
    | ncons _ a ctx' =>
      fun eq1 eq2 =>
        Ffix_kpcProd saveinfo ctx' e
          (fun e' =>
            kpcProd saveinfo a.(decl_name) e'
              (type_rename_transformer e' (a.(decl_type)))
              (fun e'' => cterm_lift _ (t (mkcinfo _ _ _ _ (ei _ _ _ _ e'') _ _ _) )))
    end
  )  eq_refl eq_refl.
Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert (n = n + 0). lia. rewrite <- H.
  destruct saveinfo.
  - destruct ci. destruct H1. auto. split. auto.
    split. simpl. 2:auto. destruct ei. simpl. constructor. auto. auto.
  - simpl. auto.
  - simpl. auto. Qed.
Next Obligation. destruct e. simpl.
  destruct saveinfo. all:simpl. all:lia. Qed.
Next Obligation. destruct e. simpl. unfold add_info_len.
  destruct saveinfo.
  - simpl. constructor. auto. auto.
  - auto.
  - auto.
Qed.
Next Obligation. lia. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + n0) = n + S n0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. lia. Qed.
Next Obligation.
  destruct e''. simpl. destruct ei. simpl. simpl in Pl.  destruct saveinfo.
  + simpl in Pl. assert (String.eqb s s  = true). apply lemstr. auto. rewrite H in Pl.
    simpl. auto.
  + auto.
  + auto.
Qed.
(* Next Obligation. *)


Program Definition it_kpcProd {n k m nind:nat} {l} (saveinfo:saveinfo)
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
    t (mkcinfo _ _ _ _ (ei _ _ _ _ e) _ _ _ )
      (mkcinfo _ _ _ _ (ei _ _ _ _ e0) _ _ _ )
  | ncons _ a ctx' => fun eq1 eq2 =>
    Ffix_mkcProd' saveinfo ctx' e e0
      (fun ea eb =>
      (* let ea' := update_kp a.(decl_name) ea saveinfo in *)
      (* let eb' := update_mk a.(decl_name) eb saveinfo in *)
        cProd a.(decl_name)
          (type_rename_transformer ea a.(decl_type))
          (cterm_lift _  $
            t
              (mkcinfo _ _ _ _ (ei _ _ _ _ (update_kp a.(decl_name) ea (Savelist saveinfo))) _ _ _)
              (mkcinfo _ _ _ _ (ei _ _ _ _ (update_mk a.(decl_name) eb (Savelist saveinfo))) _ _ _)
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
    + simpl. split.
      ++ destruct ei, ci. simpl. simpl in H0. destruct H0. eapply lemx03. 2: exact H0. lia.
      ++ destruct ei, ci. simpl. simpl in H0. destruct H0. eapply lemx04. 2: exact H1. lia.
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
  + simpl. split.
    ++ destruct ei, ci. simpl. simpl in H0. destruct H0. eapply lemx03. 2: exact H0. lia.
    ++ destruct ei, ci. simpl. simpl in H0. destruct H0. eapply lemx04. 2: exact H1. lia.
Qed.
Next Obligation.
  simpl. destruct eb. destruct ei. simpl. simpl in ck. rewrite <- lift_renaming_length. lia.
Qed.
Next Obligation.
  destruct eb. simpl. destruct ei. simpl. simpl in Pl. eapply mylem999. auto.
Qed.

Program Definition add_emp_info' {n k nind l} (infon:cinfo n k nind l) s
  : cinfo n k nind (add_info_len' l s 0) :=
  let e := ei _ _ _ _ infon in
  mkcinfo _ _ _ _
    (mkinfo e.(renaming) ((s, []) :: e.(info)) e.(info_nat) e.(info_source) e.(kn))
    _ _ _
    .
Next Obligation.
  destruct infon. simpl. split.
  + simpl. destruct ci. auto.
  + destruct ci. split.
    ++ simpl. constructor. auto. destruct H0. auto.
    ++ destruct H0. auto.
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
    [] []
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
  mkcinfo _ _ _ _ (make_initial_cinfo' kn ty) _ _ _.
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



(* Compute rels_of.
Compute rel_of. *)

(* Notation " x '<-' c1 ';;' c2" := ( c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity) : monad_scope.

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.



Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

Lemma lem777 {A} (t:A) tl: In t (List.tl tl) -> In t tl.
  induction tl.
  - simpl. auto.
  - intro. simpl in H. simpl. right. auto.
Qed.

Lemma lem888 {A} (n:nat) (t:A) (tl:list A) : In t (n_tl tl n) -> In t tl.
induction n.
- auto.
- intro. simpl in H.
  assert (In t (n_tl tl n)). eapply lem777. auto.
  exact (IHn H0).
Qed.

Definition has_info (l:list (string*nat)) str i :=
  match
    (find (fun x => String.eqb str x.1) l) with
  | Some (_, k) => i <= k
  | None => False
  end.

Lemma lem555 {l str}: mfind (replace_S l str) str > 0.
Proof.
  induction l.
  + unfold mfind. unfold replace_S. simpl.
    assert (String.eqb str str = true). apply lemstr. auto.
    rewrite H. lia.
  + simpl. destruct a. simpl.
    destruct (String.eqb t str) eqn:e.
    ++ apply lemstr in e. rewrite e. unfold mfind. simpl. auto.
       assert (String.eqb str str = true). apply lemstr. auto. rewrite H. lia.
    ++ unfold mfind. simpl.
       destruct (String.eqb str t) eqn:e1.
       -- apply lemstr in e1. rewrite e1 in e. assert (String.eqb t t = true). apply lemstr. auto.
          rewrite H in e. inversion e.
       -- simpl. auto.
Qed.

Lemma lem666 {s1 s2} l : String.eqb s1 s2 = false ->
      find
        (fun x : string × nat =>
         String.eqb s1 x.1) l
      =
      find
        (fun x : string × nat =>
        String.eqb s1 x.1)
        (replace_S l s2).
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
Qed. *)

(* Lemma has_info_within_info {} *)

(* Program Definition auxarg {n m nind l} (arg:context_decl_closed m)
  the_inductive ind_npars' (h:has_info l "P" 1)
 (ta:forall {k}, cinfo k (S m) nind (replace_S l "args") -> cterm k)
: cinfo n m nind l -> cterm n :=
  let t1 := proj1_sig arg.(decl_type) in
  let na := arg.(decl_name) in
  fun e  =>
  (match t1 as t0 return t1 = t0 -> cterm n with
  | tRel i =>
    fun eq =>
    match is_recursive_call_gen e i with
    | Some _ =>
      e <- mkcProd (Savelist "args") na e
            (existc (tInd the_inductive [])) ;;
      kpcProd NoSave the_name e
        (cterm_lift _ $ cApp (geti_info "P" e 0 _) [geti_info "args" e 0 _])
        ta
    | None =>
      kpcProd (Savelist "args") na e
        (type_rename_transformer e t1)
        ta
    end
  (*ex. vec A n*)
  | tApp (tRel i) tl =>
    fun eq =>
    match is_recursive_call_gen e i with
    | Some _ =>
      (*save the argument v into information list "args"*)
      e <- mkcProd (Savelist "args") na e
            (cApp
              (* (exist _ (tInd the_inductive []) _) *)
              (existc (tInd the_inductive []))
              (map_In tl (fun t' h' => type_rename_transformer e (existc t'))));;

      (* P n v -> [t]*)
      kpcProd NoSave the_name e
        (cterm_lift _ $ cApp
          (geti_info "P" e 0 _)
          (let tl := n_tl tl (ind_npars') in
            (map_In tl (fun t' h' => type_rename_transformer e (existc t'))) (*n*)
            ++ [geti_info "args" e 0 _(*tRel 0*)] (*v*))
        ) ta
    | None =>
      kpcProd (Savelist "args") na e
        (type_rename_transformer e t1)
        ta
    end
  | tApp _ _ => fun eq => kpcProd (Savelist "args") na e
                  (type_rename_transformer e t1)
                  ta
  | tProd na _ _ => todo
  | _ => fun eq => kpcProd (Savelist "args") na e
          (type_rename_transformer e t1)
          ta
  end) eq_refl.

Next Obligation.
  unfold has_info in h. unfold within_info. unfold mfind.
  assert (String.eqb "P" "args" = false). auto.
  pose proof (lem666 l H0).

  destruct (find
              (fun x : string × nat =>
              String.eqb "P" x.1) l) eqn:eq0.
  + rewrite <- H1. destruct p. lia.
  + inversion h.
Qed.
Next Obligation. destruct e. unfold within_info. eapply lem555. Qed.
Solve All Obligations with (destruct arg; destruct decl_type; simpl; auto).
Next Obligation. destruct arg. destruct decl_type. simpl. simpl in eq.
  rewrite eq in i0. simpl in i0.
  apply andb_andI in i0. destruct i0. apply forallb_Forall in H1.
  eapply Forall_forall in H1. 2: exact h'. auto. Qed.
Next Obligation.
  unfold has_info in h. unfold within_info. unfold mfind.
  assert (String.eqb "P" "args" = false). auto.
  pose proof (lem666 l H0).
  destruct (find
              (fun x : string × nat =>
              String.eqb "P" x.1) l) eqn:eq0.
  + rewrite <- H1. destruct p. lia.
  + inversion h.
Qed.
Next Obligation.
  destruct arg. destruct decl_type. simpl. simpl in eq.
  rewrite eq in i0. simpl in i0.
  apply andb_andI in i0. destruct i0. apply forallb_Forall in H1.
  eapply Forall_forall in H1. 2: eapply lem888. 2:exact h'. auto. Qed.
Next Obligation.    destruct e. unfold within_info. eapply lem555. Qed.
Solve All Obligations with (destruct arg; destruct decl_type; simpl; auto).
(* Next Obligation. *)
(* destruct arg. destruct decl_type. simpl. auto. Qed. *)
(* Next Obligation. *)




Program Fixpoint transformer_args {n k nind m} {l}
        (args:context_closed k m) the_inductive ind_npars' (h:has_info (add_info_len' l "args" m) "P" 1)
        (t0:forall p, cinfo p (k + m) nind (add_info_len' l "args" m) -> cterm p)
          : cinfo n k nind (add_info_len' l "args" 0) -> cterm n :=
        (match args as args0
          in context_closed _ m2
          return forall (a:m=m2), (cast args m2 a = args0)
                -> cinfo n k nind (add_info_len' l "args" 0) -> cterm n with
          | nnil => fun eq1 eq2 => fun e' => t0 _ (mkcinfo _ _ _ _ (ei _ _ _ _ e') _ _ _)
          | ncons _ a args' =>
            fun eq1 eq2 =>
              transformer_args args' the_inductive ind_npars' _
                (fun m => auxarg a the_inductive ind_npars' _
                  (fun p e'' => t0 p (mkcinfo _ _ _ _ (ei _ _ _ _ e'') _ _ _ )))
          end) eq_refl eq_refl.
Next Obligation. destruct e'. simpl. auto. Qed.
Next Obligation. destruct e'. simpl. lia. Qed.
Next Obligation. destruct e'. simpl. auto. Qed.
(* Next Obligation.  *)

Next Obligation. destruct e''. simpl. auto. Qed.
Next Obligation. destruct e''. simpl. lia. Qed.
Next Obligation. destruct e''. simpl. unfold add_info_len'. auto. Qed.
(* Next Obligation. *)
 (* destruct x. destruct x. simpl. simpl in l. auto. Qed.
Next Obligation. destruct x. destruct x. simpl. simpl in l. lia. Qed.
Next Obligation. destruct x0. destruct x0. simpl. simpl in l. auto. Qed.
Next Obligation. destruct x0. destruct x0. simpl. simpl in l. lia. Qed. *)


(* Print transformer_args. *)

Program Definition transformer_result {n k nind l} (t:cterm k) n0
  constructor_current (ch:closedn n constructor_current)
  (h:has_info l "P" 1)
  :cinfo n k nind l -> cterm n := fun e =>
  match proj1_sig t with
  | tApp (tRel i) tl =>
    match is_recursive_call_gen e i with
    | Some _ =>
      cApp
        (geti_info "P" e 0 _)
        (let tl := n_tl tl n0 in
            (map_In tl (fun t' h' => type_rename_transformer e (existc t')))
            ++
            [
              cApp (existc constructor_current )
                (rels_of "params" e ++ rels_of "args" e)
            ])
    | None => todo (*must be an error*)
    end
  | tRel i =>
    match is_recursive_call_gen e i with
    | Some _ =>
      cApp
      (geti_info "P" e 0 _)
      [ cApp (existc constructor_current )
          (rels_of "params" e ++ rels_of "args" e)
          ]
    | None => todo (*must be an error*)
    end
  | _ => todo end (*must be an error*).
Next Obligation.
  unfold within_info.
  unfold mfind.
  unfold has_info in h.
  destruct (find (fun x : string × nat => String.eqb "P" x.1) l) eqn:eq0.
  + destruct p. auto.
  + inversion h.
Qed.
Next Obligation.
  destruct t. simpl in Heq_anonymous0. rewrite <- Heq_anonymous0 in i0.
  simpl in i0. apply andb_andI in i0. destruct i0 as [ih1 ih2]. apply forallb_Forall in ih2.
  eapply Forall_forall in ih2. 2: eapply lem888. 2: exact h'. auto. Qed.
Next Obligation.
  unfold within_info.
  unfold mfind.
  unfold has_info in h.
  destruct (find (fun x : string × nat => String.eqb "P" x.1) l) eqn:eq0.
  + destruct p. auto.
  + inversion h.
Qed.
Solve All Obligations with (repeat split; repeat discriminate).
(* Next Obligation. *)

(* Print transformer_result. *)


Program Definition auxctr {n m nind l} (e:cinfo n m nind (add_info_len' l "args" 0))
  (ctr:constructor_body_closed m) (i:nat) the_inductive (ind_npars' n0:nat)
  (h:has_info (add_info_len' l "args" m) "P" 1)
  : cterm n :=
  let constructor_current : term := tConstruct the_inductive i [] in
  let cstr_type := proj1_sig (cstr_type' _ ctr) in
  let return_type :=
    (fix Ffix t :=
      match t with
      | tProd _ _ t => Ffix t
      | _ => t
      end ) cstr_type
  in
  @transformer_args _ _ _ _ l (cstr_args' _ ctr) the_inductive ind_npars' _
    (fun m => transformer_result (exist _ return_type todo) n0 constructor_current _ _)
    e
  .

(* Print auxctr. *)
(* Next Obligation. *)

Program Fixpoint Ffix_aux {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m))
  (t:cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) (i:nat)
  (the_inductive:inductive) (ind_npars' n0:nat) (h:has_info l "P" 1) {struct b}
  :cterm n:=
  (match b
    as b0 return b = b0 -> cterm n
    with
  | [] => fun eq => cterm_lift _ $ t (mkcinfo _ _ _ _ (ei _ _ _ _ e) _ _ _)
  | ctr :: b' => fun eq =>
      @mkcProd _ _ _ l NoSave the_name e
        (@auxctr _ _ _ l (add_emp_info' e "args") ctr i the_inductive ind_npars' n0 _)
        (fun e' =>
          Ffix_aux e' b'
          (fun e'' => cterm_lift _ $ t
            (mkcinfo _ _ _ _ (ei _ _ _ _ e'') _ _ _)
          )
          (i+1) the_inductive ind_npars' n0 _)
  end) eq_refl.

Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e. auto. Qed.
Next Obligation. destruct e. auto. Qed.

Next Obligation. lia. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + #|b'|) = n + S #|b'|). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. auto. Qed.
Next Obligation. destruct e''. simpl. auto. Qed.
(* Next Obligation. *)

(* Print auxarg. *)

Program Definition aux' {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m))
  (t:cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) the_inductive ind_npars n0 h: cterm n :=
  Ffix_aux e b t 0 the_inductive ind_npars n0 h.
(* Next Obligation. *)
(* Next Obligation. exact l. Qed. *)


Program Definition GenerateIndp' (na:kername)
 (ty:mutual_inductive_body_closed) (h:wf_ind_closed ty):
  cterm 0 :=
  let params := ty.(ind_params') in
  let initial_info := make_initial_cinfo na ty h in
  let body := hd todo ty.(ind_bodies') in
  let the_inductive := {| inductive_mind := na; inductive_ind := 0 |} in
  let indices := ind_indices' _ body in

  let aux {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m)) h
    (t:cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) : cterm n :=
    aux' e b t the_inductive ty.(ind_npars') (context_length params) h
  in
  e <- @it_kpcProd 0 _ _ _ _ (Savelist "params") (params) (initial_info);;
  e <- @mkcProd (context_length params) _ _  _ (Savelist "P") prop_name e
    ( (*type of P: forall (i1:Ind1) ... (im:Indm), T A1 ... Ak i1 ... im -> Prop*)
      (*forall (i1:Ind1) ... (im:Indm)*)
      e <- it_mkcProd ("indices") (indices) e;;
      e <- mkcProd NoSave the_name e
            (cApp
                (existc (tInd the_inductive []))
                (rels_of "params" e ++ rels_of "indices" e));;
      existc (tSort sProp)
    );;
  e <- aux e (ind_ctors' _ body) _;;
    e <- it_mkcProd ("indices") (indices) e;;
    e <- mkcProd (Saveitem "x") the_name e
          (cApp
              (existc (tInd the_inductive []))
              (rels_of "params" e ++ rels_of "indices" e)
          );;
      cApp (geti_info "P" e 0 _) (rels_of "indices" e ++ [rel_of "x" e])
.
Next Obligation.
  unfold has_info. simpl. auto.
Qed.
Next Obligation.
  unfold within_info. destruct e. simpl.
  unfold mfind. unfold find. simpl. auto.
Qed. *)
(* Next Obligation. *)


(* Inductive myvec (A:Type) : nat -> Type :=
 | myvnil : myvec A 0
 | myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
Definition thisfile := $run (tmCurrentModPath tt).
Definition input := ($run (tmQuoteInductive (thisfile, "myvec"))).
Definition input_closed_ := aux input.
Definition input_closed := proj1_sig input_closed_.

Definition result := GenerateIndp' (thisfile, "myvec") input_closed (proj2_sig input_closed_). *)
(* Compute input_closed. *)


(* Compute $unquote (proj1_sig result). *)

