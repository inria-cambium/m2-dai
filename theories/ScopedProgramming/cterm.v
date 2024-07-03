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

Program Fixpoint cApp {n:nat} (x:cterm n) (yl:list (cterm n)) {struct yl}:
  cterm n :=
    match yl with
    | [] => existc (proj1_sig x)
    | y :: yl => cApp (existc (tApp (proj1_sig x) [proj1_sig y])) yl
    end
  .
Next Obligation. destruct x. auto. Qed.
Next Obligation. destruct x, y. auto. Qed.

