Require Import MetaCoq.ScopedProgramming.cterm.

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


Definition context_decl_closed (n:nat) := (BasicAst.context_decl (cterm n)).

Inductive context_closed (k:nat) : nat -> Type :=
  | nnil : context_closed k 0
  | ncons : forall {n:nat},
      context_decl_closed (k + n) -> context_closed k n -> context_closed k (S n).

Program Fixpoint aux_context' n params (h:Is_closed_context n params)
  {struct params}: context_closed n #|params|:=
  (match params as params0
    return params = params0 -> context_closed n #|params0| with
  | [] => fun (eq:params = []) => nnil n
  | x :: ps => fun (eq:params = x :: ps) =>
    ncons n (
        mkdecl x.(decl_name) None (exist _ x.(decl_type) _)
      ) (aux_context' n ps _)
  end
  ) eq_refl.
Next Obligation. inversion h. auto. Qed.
Next Obligation. inversion h. auto. Qed.
(* Next Obligation. *)

Record constructor_body_closed (n:nat) := Build_constructor_body_closed {
  cstr_name' : ident;
  cstr_arity' : nat;
  cstr_args' : context_closed n cstr_arity';
  cstr_indices' : list (cterm (n + cstr_arity'));
  cstr_type' : cterm n;
}.

Program Definition aux_constructor_body' n ctor (h:Is_closed_constructor n ctor)
  : constructor_body_closed n :=
  Build_constructor_body_closed n
    ctor.(cstr_name)
    #|ctor.(cstr_args)|
    (aux_context' n ctor.(cstr_args) _)
    (map_In ctor.(cstr_indices) (fun t h' => exist _ t _) )
    (exist _ ctor.(cstr_type) _)
    .
Next Obligation. inversion h. auto. Qed.
Next Obligation.
  destruct h as [Harg Htyp Hindices]. eapply Forall_forall in Hindices.
  2: exact h'. auto.
Qed.
Next Obligation. destruct h. auto. Qed.


Record one_inductive_body_closed (n:nat) := Build_one_inductive_body_closed {
  ind_name' : ident;
  n_indices' : nat;
  ind_indices': context_closed n n_indices';
  ind_sort' : sort;
  ind_type' : cterm n;
  ind_kelim' : allowed_eliminations;
  ind_ctors' : list (constructor_body_closed n);
  ind_projs' : list projection_body;
  ind_relevance' : relevance
}.

Program Definition aux_one_inductive' (n:nat) (body:one_inductive_body)
  (h:Is_closed_body n body) : one_inductive_body_closed n :=
  Build_one_inductive_body_closed n
    body.(ind_name)
    #|body.(ind_indices)|
    (aux_context' n body.(ind_indices) _)
    body.(ind_sort)
    (exist _ body.(ind_type) _)
    body.(ind_kelim)
    (map_In body.(ind_ctors) (fun ctrs h' => aux_constructor_body' n ctrs _) )
    body.(ind_projs)
    body.(ind_relevance).
Next Obligation. destruct h. auto. Qed.
Next Obligation. destruct h. auto. Qed.
Next Obligation.
  destruct h as [Hindices Hctors Hindtyp].
  eapply Forall_forall in Hctors. 2: exact h'. auto.
Qed.
(* Next Obligation. *)

Record mutual_inductive_body_closed : Type := Build_mutual_inductive_body_closed
  { ind_finite' : recursivity_kind;
    ind_npars' : nat;
    nind' : nat;
    ind_params': context_closed nind' ind_npars';
    ind_bodies' : list (one_inductive_body_closed (nind' + ind_npars'));
    ind_universes' : universes_decl;
    ind_variance' : option (list Variance.t) }.

Definition context_length {m n} (p:context_closed m n) : nat := n.

Definition wf_ind_closed ty : Prop :=
  ty.(nind') = #|ty.(ind_bodies')|
  /\ ty.(ind_npars') = context_length ty.(ind_params')
  .

Lemma map_In_length {A B} l (f:forall x:A, In x l -> B):
  #|l| = #|map_In l f|.
Proof.
  revert f.
  induction l.
  - auto.
  - intro g. simpl.
    rewrite <- IHl. auto.
Qed.


(*API*)
Program Definition get_cbody (ty:mutual_inductive_body) (h:Is_closed_mutual_ind_body ty):
  {ty: mutual_inductive_body_closed | wf_ind_closed ty} :=
  let nind := #|ty.(ind_bodies)| in
  exist _
  (Build_mutual_inductive_body_closed
    ty.(ind_finite)
    #|ty.(ind_params)|
    nind
    (aux_context' nind ty.(ind_params) _)
    (map_In ty.(ind_bodies) (fun body h' => aux_one_inductive' (nind + #|ty.(ind_params)|) body _))
    ty.(ind_universes)
    ty.(ind_variance)) _
    .
Next Obligation. destruct h. auto. Qed.
Next Obligation.
  destruct h. eapply Forall_forall in is_closed_body0.
  2: exact h'. auto.
Qed.
Next Obligation.
  split. simpl.
  - rewrite <- map_In_length. auto.
  - auto.
Qed.

