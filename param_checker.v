Require Import BasePrelude.

Definition and_listbool (l:list bool) (l':list bool) :=
  map2 (fun a b => andb a b) l l'.

Definition CheckUniformParam (kn:kername) (ty:mutual_inductive_body) : list bool :=
  let params := ty.(ind_params) in
  let npars := length params in
  let res := repeat true npars in
  let initial_info := make_initial_info kn ty in
  fold_update_kp_util (Savelist "params") (rev params) initial_info
    (fun _ bl => bl)
    (fun e =>
      fold_right (fun body bl' =>
        fold_right (
          fun ctr bl =>
            let fix Ffix args e bl :=
              let aux arg e bl:=
                let t := arg.(decl_type) in
                match t with
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
                | _ => bl end
              in
              match args with
              | [] => bl
              | arg :: l =>
                  update_kp_util NoSave arg.(decl_name) e
                    (fun e => aux arg e) (fun e => Ffix l e bl)
            end in
            Ffix (rev ctr.(cstr_args)) e bl
        ) bl' body.(ind_ctors))
      res ty.(ind_bodies)
    )
  .

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
