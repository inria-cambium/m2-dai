Require Import MetaCoq.ScopedProgramming.cterm.

(* Global Open Scope bs. *)



Section Is_closed.

  Inductive Is_closed_context : context -> nat -> Prop :=
    | closednil : forall n, Is_closed_context [] n
    | closedcons (a:context_decl) (n:nat) (l:context):
        Is_closed_context l n -> closedn (n + #|l|) (decl_type a) ->
        Is_closed_context (a :: l) n.

  Record Is_closed_constructor (ctor:constructor_body) (n:nat): Prop :={
    is_closed_args : Is_closed_context (cstr_args ctor) n;
    is_closed_cstr_type: closedn n (cstr_type ctor);
  }.

  Record Is_closed_body (body:one_inductive_body) (n:nat): Prop :={
    is_closed_indices : Is_closed_context (ind_indices body) n;
    is_closed_constructors :
      Forall (fun ctor => Is_closed_constructor ctor n)(ind_ctors body);
  }.

  Record Is_closed_mutual_ind_body (ty:mutual_inductive_body) : Prop :={
    is_closed_params : Is_closed_context (ind_params ty) 0;
    is_closed_body:
      Forall
        (fun ind_body =>
          Is_closed_body ind_body (#|ind_params ty| + #|ind_bodies ty|))
        (ind_bodies ty);
  }.
End Is_closed.


Definition context_decl_closed (n:nat) := (BasicAst.context_decl (cterm n)).

Inductive context_closed (k:nat) : nat -> Type :=
  | nnil : context_closed k 0
  | ncons : forall {n:nat},
      context_decl_closed (k + n) -> context_closed k n -> context_closed k (S n).


Fixpoint aux_context n (params:context) : context_closed n #|params| :=
  (match params as params0
    return params = params0 -> context_closed n #|params0| with
  | [] => fun (eq:params = []) => nnil n
  | x :: ps => fun (eq:params = x :: ps) =>
    ncons n (
        mkdecl x.(decl_name) None (exist _ x.(decl_type) todo)
      ) (aux_context n ps)
  end
  ) eq_refl.

Record constructor_body_closed (n:nat) := Build_constructor_body_closed {
  cstr_name' : ident;
  cstr_arity' : nat;
  cstr_args' : context_closed n cstr_arity';
  cstr_indices' : list (cterm (n + cstr_arity'));
  cstr_type' : cterm n;

}.




Program Definition aux_constructor_body n body
  : constructor_body_closed n :=
  Build_constructor_body_closed n
    body.(cstr_name)
    #|body.(cstr_args)|
    (aux_context n body.(cstr_args))
    (map (fun t => exist _ t todo) body.(cstr_indices))
    (exist _ body.(cstr_type) todo)
    .


Record one_inductive_body_closed (n:nat) := Build_one_inductive_body_closed {
  ind_name' : ident;
  n_indices' : nat;
	(* ind_indices' : @sigT nat (fun m => context_closed n m); *)
  ind_indices': context_closed n n_indices';

  (* eq_indices' : projT1 ind_indices' = n_indices'; *)

  ind_sort' : sort;
  ind_type' : cterm n;
  ind_kelim' : allowed_eliminations;
  ind_ctors' : list (constructor_body_closed n);
  ind_projs' : list projection_body;
  ind_relevance' : relevance
}.

Program Definition aux_one_inductive (n:nat) (body:one_inductive_body) :
  one_inductive_body_closed n :=
  Build_one_inductive_body_closed n
    body.(ind_name)
    #|body.(ind_indices)|
    (* (existT _ _ (aux_context n body.(ind_indices)))
    _ *)
    (aux_context n body.(ind_indices))
    body.(ind_sort)
    (exist _ body.(ind_type) todo)
    body.(ind_kelim)
    (map (fun ctrs => aux_constructor_body n ctrs) body.(ind_ctors))
    body.(ind_projs)
    body.(ind_relevance).



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


Definition aux_ind_bodies n (ind_bodies:list (one_inductive_body))
  : list (one_inductive_body_closed n) :=
  map (fun ind_body => aux_one_inductive n ind_body) ind_bodies.


Program Definition get_cbody (ty:mutual_inductive_body):
  {ty: mutual_inductive_body_closed | wf_ind_closed ty} :=
  let nind := #|ty.(ind_bodies)| in
  exist _
  (Build_mutual_inductive_body_closed
    ty.(ind_finite)
    #|ty.(ind_params)|
    nind
    (aux_context nind ty.(ind_params))
    (* (existT _ _ (aux_context nind ty.(ind_params)))
    _ *)
    (aux_ind_bodies (nind + #|ty.(ind_params)|) ty.(ind_bodies))
    ty.(ind_universes)
    ty.(ind_variance)) _
    .
Next Obligation.
  split. simpl.
  - unfold aux_ind_bodies. rewrite (map_length _). auto.
  - simpl. tauto.
Qed.

