(*
  give another style of using the framework
    (no kptbind any more, users should use only mktbind)
*)
Require Import MetaCoq.Programming.BasePrelude.

Definition fold_bodies (auxbody: nat -> one_inductive_body -> (infolocal -> term) -> infolocal -> term)
  (l:list one_inductive_body) (t0:infolocal -> term) : infolocal -> term :=
  fold_right_ie auxbody l t0.

Definition fold_ctrs (auxctr: nat -> constructor_body -> (infolocal -> term) -> infolocal -> term)
  (l:list constructor_body) (t0:infolocal -> term) : infolocal -> term :=
  fold_right_ie auxctr l t0.

Definition fold_args (auxarg: BasicAst.context_decl term -> (infolocal -> term) -> infolocal -> term)
  (l:context)
  (t0:infolocal -> term) : infolocal -> term :=
  let fix aux l t : infolocal -> term :=
    match l with
    | [] => t
    | a :: l => aux l
      (auxarg a (fun e => t (next (decl_name a) (decl_body a) e)))
    end in
  aux l t0.

Definition fold_params (auxparam: BasicAst.context_decl term -> (infolocal -> term) -> infolocal -> term)
  (l:context) (t0:infolocal -> term) : infolocal -> term :=
  let fix aux l t : infolocal -> term :=
    match l with
    | [] => t
    | a :: l => aux l
      (auxparam a (fun e => t (next (decl_name a) (decl_body a) e)))
    end in
  aux l t0.

Definition fold_indices (auxindice: BasicAst.context_decl term -> (infolocal -> term) -> infolocal -> term)
  (l:context) (t0:infolocal -> term) : infolocal -> term :=
  let step_back (e:infolocal) : infolocal :=
    let info_source :=
      map (
        fun x => match x with
        | (na, information_list l) => (na, information_list (minus_one_index l))
        | (na, information_nat n) => (na, information_nat (n-1)) end
      ) e.(info_source)
    in
    let renaming := tl e.(renaming) in
    mkinfo renaming e.(info) info_source e.(kn)
  in
  let fix aux l t : infolocal -> term :=
    match l with
    | [] => t
    | a :: l =>
      aux l (auxindice a (fun e => t (next (decl_name a) (decl_body a) e)))
    end in
  aux l (fun e => t0 (redo step_back #|l| e)).
