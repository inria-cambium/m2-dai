Require Import BasePrelude.

Definition and_listbool (l:list bool) (l':list bool) :=
  map2 (fun a b => andb a b) l l'.

Definition visit_args {X} (kn:kername) (ty:mutual_inductive_body)
  (init:X) (aux:context_decl->extrainfo->X->X): X:=
  let initial_info := make_initial_info kn ty in
  let params := ty.(ind_params) in
  let npars := length params in
  let initial_info := make_initial_info kn ty in
  fold_update_kp_util (Savelist "params") (params) initial_info
    (fun _ x => x)
    (fun e =>
      fold_left (fun x body =>
        fold_left (fun y ctr =>
          let fix Ffix args e y :=
            match args with
            | [] => y
            | arg :: l =>
              update_kp_util NoSave arg.(decl_name) e
                (aux arg) (fun e => Ffix l e y)
            end in
          Ffix (rev ctr.(cstr_args)) e y) body.(ind_ctors) x
      ) ty.(ind_bodies) init
    ).


Definition CheckUniformParam (kn:kername) (ty:mutual_inductive_body) : list bool :=
  let npars := length ty.(ind_params) in
  let init := repeat true npars in
  let fix aux argtype e bl: list bool:=
    match argtype with
    | tApp (tRel i) tl =>
      match is_recursive_call_gen e i with
      | Some _ =>
        and_listbool bl
          (mapi (
            fun i t =>
              match t with
              | tRel k =>
                  if tRel k == (geti_info "params" e (npars-1-i))
                  then true else false
              | _ => false end
            ) (firstn npars tl))
      | None => bl
      end
    | tProd na t1 t2 =>
        update_kp_util NoSave na e (fun e y => y) (fun e => aux t2 e bl)
    | _ => bl end
  in
  visit_args kn ty init (fun arg e x => aux arg.(decl_type) e x).

Definition thisfile := $run (tmCurrentModPath tt).

Inductive myvec (A:Type) : nat -> Type :=
| myvnil : myvec A 0
| myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
Definition input := ($run (tmQuoteInductive (thisfile, "myvec"))).
Compute (CheckUniformParam (thisfile, "myvec") input).

Inductive le: nat -> nat -> Type :=
| le_refl n : le n n
| le_S n m : le (S n) m -> le n m.
Definition input_le := ($run (tmQuoteInductive (thisfile, "le"))).
Compute (CheckUniformParam (thisfile, "le") input_le).

Inductive le'  (A:Type)(n : nat) (B:Type): nat -> Type :=
| le_refl' : le'   A n B n
| le_S' m : le' A (S n)  (A*B) m -> le'  (A) n B n ->le' A n  B m.
Definition input_le':= ($run (tmQuoteInductive (thisfile, "le'"))).
Compute (CheckUniformParam (thisfile, "le'") input_le').

Inductive le0' (n : nat): nat -> Type :=
| le0_refl' : le0'  n  n
| le0_S' m : le0' n  m -> le0' n n ->le0' n  m
with smt (n:nat) : Type := STH (m:nat) (_:smt m) : smt n
.
Definition input_le0':= ($run (tmQuoteInductive (thisfile, "le0'"))).
Compute (CheckUniformParam (thisfile, "le0'") input_le0').
(* Check le0'_ind. *)


Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
	Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.
Definition input_acc:= ($run (tmQuoteInductive (thisfile, "Acc"))).
Compute (CheckUniformParam (thisfile, "Acc") input_acc).

