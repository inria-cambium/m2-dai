Require Import BasePrelude.

Definition and_listbool (l:list bool) (l':list bool) :=
  map2 (fun a b => andb a b) l l'.

Definition CheckUnifomParam (kn:kername) (ty:mutual_inductive_body) : list bool :=
  let params := ty.(ind_params) in
  let npars := length params in
  let res := repeat true npars in
  let body := hd todo ty.(ind_bodies) in
  let ctrs := body.(ind_ctors) in

  let initial_info := make_initial_info kn ty in
  it_kptProd_util (Savelist "params") (rev params) initial_info
    (fun _ bl => bl)
    (fun e =>
      fold_right (
        fun ctr bl =>
          let args := ctr.(cstr_args) in
          let fix Ffix args e bl :=
            let aux arg e bl:=
              let t := arg.(decl_type) in
              match t with
              | tApp (tRel i) tl =>
                (* print_info e *)
                (* printi i *)
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
                kptProd_util NoSave arg.(decl_name) e
                  (fun e => aux arg e) (fun e => Ffix l e bl)
          end in
          Ffix (rev args) e bl
      ) res ctrs)
  .

Definition thisfile := $run (tmCurrentModPath tt).

Inductive myvec (A:Type) : nat -> Type :=
| myvnil : myvec A 0
| myvcons (x:A) (n:nat) (v:myvec A n) : myvec A (S n).
Definition input := ($run (tmQuoteInductive (thisfile, "myvec"))).
Compute (CheckUnifomParam (thisfile, "myvec") input).

Inductive le: nat -> nat -> Type :=
| le_refl n : le n n
| le_S n m : le (S n) m -> le n m.
Definition input_le := ($run (tmQuoteInductive (thisfile, "le"))).
Compute (CheckUnifomParam (thisfile, "le") input_le).

Inductive le'  (A:Type)(n : nat) (B:Type): nat -> Type :=
| le_refl' : le'   A n B n
| le_S' m : le' A (S n)  (A*B) m -> le'  (A) n B n ->le' A n  B m.
Definition input_le':= ($run (tmQuoteInductive (thisfile, "le'"))).
Compute (CheckUnifomParam (thisfile, "le'") input_le').


(* Search (nat ->  list _ -> list _ ).
Print skipn.
Print firstn. *)
(* Print find.
Search (( _ -> bool) -> list _ -> option _). *)

Definition findi {X} (f: X -> bool) (l:list X) :option nat :=
  let fix Ffix l n:=
    match l with
    | [] => None
    | y :: l' => if f y then Some n else Ffix l' (n+1)
    end
  in
  Ffix l 0.

Print firstn.

Definition SeperateParams (kn:kername) (ty:mutual_inductive_body) :=
  let params := ty.(ind_params) in
  let bl := CheckUnifomParam kn ty in
  match findi (fun b => negb b) bl with
  | None => (params, [])
  | Some i => (skipn (length params - i) params, firstn (length params - i) params)
  end.

Print SeperateParams.

Compute (SeperateParams (thisfile, "le'") input_le').
