Require Import MetaCoq.ScopedProgramming.
Global Open Scope bs.
Import Lia.

Definition the_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |}.
Definition prop_name := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.



Fixpoint n_tl {A} (l:list A) n :=
  match n with
  | 0 => l
  | S n => List.tl (n_tl l n)
  end
.

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

Definition has_info (l:list (string*nat)) str i :=
  match
    (find (fun x => String.eqb str x.1) l) with
  | Some (_, k) => i <= k
  | None => False
  end.

Lemma lem_arg0 {l str}: mfind (replace_S l str) str > 0.
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

Lemma lem_arg1 {s1 s2} l : String.eqb s1 s2 = false ->
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
Qed.


Program Definition auxarg {n m nind l} (arg:context_decl_closed m)
  kn ind_npars' (h:has_info l "P" nind)
 (ta:forall {k}, cinfo k (S m) nind (replace_S l "args") -> cterm k)
: cinfo n m nind l -> cterm n :=
  let t1 := proj1_sig arg.(decl_type) in
  let na := arg.(decl_name) in
  fun e  =>
  (match t1 as t0 return t1 = t0 -> cterm n with
  | tRel i =>
    fun eq =>
    match is_rec_call e i with
    | Some kk =>
      e <- mkcProd (Some "args") na e
            (existc (tInd {| inductive_mind := kn; inductive_ind := nind -1 - kk |} [])) ;;
      kpcProd None the_name e
        (cterm_lift _ $ cApp (geti_info "P" e (proj1_sig kk) _) [geti_info "args" e 0 _])
        ta
    | None =>
      kpcProd (Some "args") na e
        (rename e t1)
        ta
    end
  (*ex. vec A n*)
  | tApp (tRel i) tl =>
    fun eq =>
    match is_rec_call e i with
    | Some kk =>
      (*save the argument v into information list "args"*)
      e <- mkcProd (Some "args") na e
            (cApp
              (* (exist _ (tInd the_inductive []) _) *)
              (existc (tInd {| inductive_mind := kn; inductive_ind := nind -1 - kk |} []))
              (map_In tl (fun t' h' => rename e (existc t'))));;

      (* P n v -> [t]*)
      kpcProd None the_name e
        (cterm_lift _ $ cApp
          (geti_info "P" e (proj1_sig kk) _)
          (let tl := n_tl tl (ind_npars') in
            (map_In tl (fun t' h' => rename e (existc t'))) (*n*)
            ++ [geti_info "args" e 0 _(*tRel 0*)] (*v*))
        ) ta
    | None =>
      kpcProd (Some "args") na e
        (rename e t1)
        ta
    end
  | tApp _ _ => fun eq => kpcProd (Some "args") na e
                  (rename e t1)
                  ta
  | tProd na _ _ => (*todo*)
          fun eq => kpcProd (Some "args") na e
                          (rename e t1)
                          ta
  | _ => fun eq => kpcProd (Some "args") na e
          (rename e t1)
          ta
  end) eq_refl.

Next Obligation.
  unfold has_info in h. unfold within_info. unfold mfind.
  assert (String.eqb "P" "args" = false). auto.
  pose proof (lem_arg1 l H0).

  destruct (find
              (fun x : string × nat =>
              String.eqb "P" x.1) l) eqn:eq0.
  + rewrite <- H1. destruct p. lia.
  + inversion h.
Qed.
Next Obligation. destruct e. unfold within_info. eapply lem_arg0. Qed.
Solve All Obligations with (destruct arg; destruct decl_type; simpl; auto).
Next Obligation. destruct arg. destruct decl_type. simpl. simpl in eq.
  rewrite eq in i0. simpl in i0.
  apply andb_andI in i0. destruct i0. apply forallb_Forall in H1.
  eapply Forall_forall in H1. 2: exact h'. auto. Qed.
Next Obligation.
  unfold has_info in h. unfold within_info. unfold mfind.
  assert (String.eqb "P" "args" = false). auto.
  pose proof (lem_arg1 l H0).
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
  eapply Forall_forall in H1. 2: eapply lem_ntl1. 2:exact h'. auto. Qed.
Next Obligation.    destruct e. unfold within_info. eapply lem_arg0. Qed.
Solve All Obligations with (destruct arg; destruct decl_type; simpl; auto).


Program Fixpoint transformer_args {n k nind m} {l}
        (args:context_closed k m) kn ind_npars' (h:has_info (add_info_len' l "args" m) "P" nind)
        (t0:forall p, cinfo p (k + m) nind (add_info_len' l "args" m) -> cterm p)
          : cinfo n k nind (add_info_len' l "args" 0) -> cterm n :=
        (match args as args0
          in context_closed _ m2
          return forall (a:m=m2), (cast args m2 a = args0)
                -> cinfo n k nind (add_info_len' l "args" 0) -> cterm n with
          | nnil => fun eq1 eq2 => fun e' => t0 _ (mkcinfo (ei e') _ _ _)
          | ncons _ a args' =>
            fun eq1 eq2 =>
              transformer_args args' kn ind_npars' _
                (fun m => auxarg a kn ind_npars' _
                  (fun p e'' => t0 p (mkcinfo (ei e'') _ _ _ )))
          end) eq_refl eq_refl.
Next Obligation. destruct e'. simpl. auto. Qed.
Next Obligation. destruct e'. simpl. lia. Qed.
Next Obligation. destruct e'. simpl. auto. Qed.
(* Next Obligation.  *)

Next Obligation. destruct e''. simpl. auto. Qed.
Next Obligation. destruct e''. simpl. lia. Qed.
Next Obligation. destruct e''. simpl. unfold add_info_len'. auto. Qed.
(* Next Obligation. *)

Program Definition transformer_result {n k nind l} j
  constructor_current indices
  (h:has_info l "P" nind) (hj: j < nind)
  :cinfo n k nind l -> cterm n := fun e =>
  cApp (geti_info "P" e j _)
    (
      (map (rename e) indices)
      ++
      [cApp constructor_current
        (rels_of "params" e ++ rels_of "args" e)]
    ).
Next Obligation.
  unfold within_info. unfold mfind.
  unfold has_info in h.
  destruct (find (fun x : string × nat => String.eqb "P" x.1) l) eqn:eq0.
  + destruct p. lia.
  + inversion h.
Qed.
(* Next Obligation. *)



Program Definition auxctr {n m nind l} (e:cinfo n m nind (add_info_len' l "args" 0))
  (ctr:constructor_body_closed m) (j i:nat) kn (ind_npars':nat) (hj:j<nind)
  (h:has_info (add_info_len' l "args" m) "P" nind)
  : cterm n :=
  let the_inductive := {|inductive_mind := kn; inductive_ind := nind - j - 1|} in
  let constructor_current : term := tConstruct the_inductive i [] in
  (* let cstr_type := proj1_sig (cstr_type' _ ctr) in
  let return_type :=
    (fix Ffix t :=
      match t with
      | tProd _ _ t => Ffix t
      | _ => t
      end ) cstr_type
  in *)
  @transformer_args _ _ _ _ l (cstr_args' _ ctr) kn ind_npars' _
    (fun m =>
      transformer_result
        j (existc constructor_current) (cstr_indices' _ ctr) _ _)
    e
  .
(* Next Obligation. *)


Program Fixpoint Ffix_aux {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m))
  (j:nat) (t:cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) (i:nat)
  (kn:kername )(ind_npars':nat) (h:has_info l "P" nind) (hj:j<nind) {struct b}
  :cterm n:=
  (match b
    as b0 return b = b0 -> cterm n
    with
  | [] => fun eq => cterm_lift _ $ t (mkcinfo (ei e) _ _ _)
  | ctr :: b' => fun eq =>
      @mkcProd _ _ _ l None the_name e
        (@auxctr _ _ _ l (add_emp_info' e "args") ctr j i kn ind_npars' _ _)
        (fun e' =>
          Ffix_aux e' b' j
          (fun e'' => cterm_lift _ $ t
            (mkcinfo (ei e'') _ _ _)
          )
          (S i) kn ind_npars' _ _)
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


Program Definition aux' {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m))
  (j:nat) (t:cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) kn ind_npars h hj: cterm n :=
  Ffix_aux e b j t 0 kn ind_npars h hj.
(* Next Obligation. *)


Program Fixpoint auxnew {n k nind l} i lb kn
  (a0 : cinfo (n + #|lb|) k nind (add_info_len' l "P" #|lb|) -> cterm (n + #|lb|)) :
  cinfo n k nind (add_info_len' l "P" 0) -> cterm n :=

 (match lb as lb' return lb = lb' -> cinfo n k nind (add_info_len' l "P" 0) -> cterm n with
 | [] => fun eq => fun e' =>
    cterm_lift _ $ (a0 (mkcinfo (ei e') _ _ _ ))
 | body :: lb' => fun eq =>
   auxnew (S i) lb' kn
     (fun e (*cinfo ( n + #|lb'|) k nind ... *) =>
       let the_inductive := {| inductive_mind := kn; inductive_ind := nind - i -1 |} in
       let indices := ind_indices' _ body in
       mkcProd (Some "P") prop_name e
         (it_mkcProd ("indices") (indices) e $
           fun e'' => cProd the_name
             (cApp (existc (tInd the_inductive []))
               (rels_of "params" e'' ++ rels_of "indices" e''))
             (existc (tSort sProp))
         )
         (fun e'' => cterm_lift _ $ a0 (mkcinfo (ei e'') _ _ _ )))
   end) eq_refl.
Next Obligation. lia. Qed.
Next Obligation. destruct e'. simpl. assert (n = n + 0). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e'. simpl. auto. Qed.
Next Obligation. destruct e'. simpl. auto. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + #|lb'|) = n + S #|lb'|). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. assert (S (n + #|lb'|) = n + S #|lb'|). lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. simpl. auto. Qed.
Next Obligation. destruct e''. simpl. auto. Qed.

Fixpoint sum' {m} (bl:list (one_inductive_body_closed m)) :=
  match bl with
  | [] => 0
  | b :: bl' => (sum' bl') + #|ind_ctors' _ b| end.

Program Definition GenerateIndp_mutual (kername : kername)
 (ty :  mutual_inductive_body_closed) (h:wf_ind_closed ty) : cterm 0 :=
  let params := ind_params' ty in
  let initial_info := make_initial_cinfo kername ty h in
  let bodies := ind_bodies' ty in
  let n_ind := #|bodies| in
  match Nat.ltb 0 n_ind with
  | false => existc (tSort sProp)
  | true =>
  let aux {n m nind l} (e:cinfo n m nind l) (b:list (constructor_body_closed m)) h
    (j:nat) hj (t: cinfo (n + #|b|) m nind l -> cterm (n + #|b|)) : cterm n :=
    aux' e b j t kername ty.(ind_npars') h hj
  in

  let fix fold_right_i_aux {n m nind l} bl i h (hi:i + #|bl| <= nind)
    (t: cinfo (n + sum' bl) m nind l -> cterm (n + sum' bl)):
    cinfo n m nind l -> cterm n
    :=
    match bl with
    | [] => fun e => cterm_lift _ $  t (mkcinfo (ei e) _ _ _ )
    | b :: bl' => fun e => cterm_lift _ $
      fold_right_i_aux bl' (S i) h _ (
        fun e' => cterm_lift _ $
          aux e' (ind_ctors' _ b) h i _
              (fun e'' =>
                cterm_lift _ $ t (mkcinfo (ei e'') _ _ _ ))
      ) e end
  in

  let mainbody := hd todo bodies in
  let indices_main := ind_indices' _ mainbody in
  let the_inductive_main := {| inductive_mind := kername; inductive_ind := 0|} in

  it_kpcProd (Some "params") (params) initial_info $
    (fun e1 =>
      @auxnew _ _ _ _ 0 (rev bodies) kername
      (* (fun e => existc (tSort sProp)) *)
        (fold_right_i_aux  (rev bodies) 0 _ _
            (
            fun e => it_mkcProd ("indices") (indices_main) e $
            fun e =>
              mkcProd (Some "x") the_name e
                (cApp (tInd the_inductive_main [])
                  (rels_of "params" e ++ rels_of "indices" e))
              (fun e => cApp (geti_info "P" e (n_ind - 1 (*todo*)) _)
                (rels_of "indices" e ++ [rel_of "x" e _])))
        )

        (add_emp_info' e1 "P")
    )
  end
  .

Next Obligation. lia. Qed.
Next Obligation. destruct e. simpl. assert  (n + 0 = n). lia. rewrite H. auto. Qed.
Next Obligation. destruct e. auto. Qed.
Next Obligation. destruct e. auto. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. destruct e''. simpl.
  assert (n + sum' bl' + #|ind_ctors' m b| = n + (sum' bl' + #|ind_ctors' m b|)).
  lia. rewrite <- H. auto. Qed.
Next Obligation. destruct e''. auto. Qed.
Next Obligation. destruct e''. auto. Qed.
Next Obligation.
  unfold has_info. simpl. destruct h.
  rewrite rev_length. lia.
Qed.
Next Obligation. rewrite rev_length. destruct h. lia. Qed.
Next Obligation.
  unfold within_info. unfold mfind. simpl. rewrite rev_length.
  apply eq_sym in Heq_anonymous.
  apply Compare_dec.leb_complete in Heq_anonymous. lia.
Qed.
Next Obligation. unfold within_info. unfold mfind. simpl. lia. Qed.


Definition kn_myProjT2 :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT2").

Definition generate_indp {A} (a : A) (out : option ident): TemplateMonad unit :=
  $let t := tmQuote a in
    match t with
    | (tInd ind u) =>
      let kn := ind.(inductive_mind) in
      $let mind := tmQuoteInductive kn in
      let cbody := get_cbody mind in
      let id := GenerateIndp_mutual kn (proj1_sig cbody) (proj2_sig cbody) in
      $let u := tmUnquote (proj1_sig id) in
      $let r := tmEval (unfold kn_myProjT2) (my_projT2 u) in
        match out with
        | Some name => tmDefinitionRed name (Some hnf) r ;; tmPrint r ;; ret tt
        | None => tmPrint r
        end
    | _ => tmFail "no inductive"
    end.

Notation "'Derive' 'InductivePrinciple' a 'as' id" := (generate_indp a (Some id)) (at level 0).
