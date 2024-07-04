Require Export MetaCoq.MetaCoqPrelude.
Export MCMonadNotation.
Export List.
Export ListNotations.

Notation "a $ b" := (a b) (at level 100, right associativity, only parsing).
Notation "'existc' x" := (exist _ x _) (at level 100).
Notation "'$let' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
                                     (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.
Notation "'try' '$let' ' x ':=' c1 'in' c2 'else' c3" := (@bind _ _ _ _ c1 (fun y =>
                                                              (match y with x => c2
                                                                       | _ => c3
                                                               end)))
                                         (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.
Notation " x '<-' c1 ';;' c2" := ( c1 (fun x => c2))
                                    (at level 100, c1 at next level, right associativity) : monad_scope.

Axiom todo : forall {A}, A.

Definition cterm (n:nat) := {t: term | closedn n t}.

Program Definition cterm_lift {n m:nat}: n <= m -> cterm n -> cterm m :=
  fun p t => existc (proj1_sig t).
Obligation 1.
  eapply closed_upwards. exact (proj2_sig t). auto.
Defined.


Program Definition cProd :forall {n:nat}, aname -> cterm n -> cterm (S n) -> cterm n :=
  fun n na t1 t2 => existc (tProd na (proj1_sig t1) (proj1_sig t2)).
Obligation 1.
  destruct t1, t2.
  simpl. auto.
Defined.

Program Definition cLambda :forall {n:nat}, aname -> cterm n -> cterm (S n) -> cterm n :=
  fun n na t1 t2 => existc (tLambda na (proj1_sig t1) (proj1_sig t2)).
Next Obligation.
  destruct t1, t2. auto.
Qed.

Program Fixpoint cApp {n:nat} (x:cterm n) (yl:list (cterm n)) {struct yl}:
  cterm n :=
    match yl with
    | [] => existc (proj1_sig x)
    | y :: yl => cApp (existc (tApp (proj1_sig x) [proj1_sig y])) yl
    end
  .
Next Obligation. destruct x. auto. Qed.
Next Obligation. destruct x, y. auto. Qed.


(********************************************)
(*not really used term*)

Program Definition cVar {n:nat} ident : cterm n := existc (tVar ident).

Program Definition cEvar {n:nat} (m:nat) (yl:list (cterm n)) : cterm n :=
  existc (tEvar m (map (fun t => proj1_sig t) yl)).
Next Obligation.
  eapply forallb_Forall.
  apply Forall_forall.
  intro. intro.
  induction yl.
  - auto.
  - simpl in H. destruct H.
    + destruct a. simpl in H. rewrite <- H. auto.
    + auto.
Qed.

Program Definition cSort {n:nat} sort : cterm n := existc (tSort sort).

Program Definition cCast {n:nat} (c:cterm n) (ck:cast_kind) (t:cterm n) : cterm n :=
  existc (tCast (proj1_sig c) ck (proj1_sig t)).
Next Obligation.
  destruct c, t. auto.
Qed.

Program Definition cLetIn {n:nat} na (b:cterm n) (t0:cterm n) (b':cterm (S n)) : cterm n :=
  existc (tLetIn na (proj1_sig b) (proj1_sig t0) (proj1_sig b')).
Next Obligation. destruct b, t0, b'. auto. Qed.

Program Definition cConst {n:nat} kn instance : cterm n := existc (tConst kn instance).

Program Definition cInd {n:nat} inductive instance : cterm n := existc (tInd inductive instance).

Program Definition cConstruct {n:nat} inductive m instance : cterm n := existc (tConstruct inductive m instance).

(* Program Definition cCase {n:nat} (ci:case_info) (p: c brs *)

Program Definition cProj {n} projection (t:cterm n) : cterm n := existc (tProj projection (proj1_sig t)).
Next Obligation. destruct t. auto. Qed.

(* Program Definition cFix {n} *)

(* Program Definition cCoFix {n}  *)

Program Definition cInt {n} i : cterm n := existc (tInt i).

Program Definition cFloat {n} f : cterm n := existc (tFloat f).

Program Definition cArray {n:nat} level (arr:list (cterm n)) (def:cterm n) (ty:cterm n) : cterm n :=
  existc (tArray level (map (fun t => proj1_sig t) arr) (proj1_sig def) (proj1_sig ty) ).
Next Obligation.
  destruct def, ty.
  simpl.
  assert (forallb (closedn n) (map (fun t : {t : term | closedn n t} => proj1_sig t) arr)).
  - apply forallb_Forall. apply Forall_forall.
    intros. induction arr.
    + auto. + destruct H. ++ destruct a. simpl in H. rewrite <- H. auto. ++ auto.
  - auto.
Qed.

