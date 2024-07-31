Require Import MetaCoq.Programming.BasePrelude.

(* Print update_kp. *)

Section visit.
  Context (X: Type).
  Context (visit_arg : context_decl -> infolocal * X -> infolocal * X).

  Definition visit_ctr : constructor_body -> infolocal * X -> infolocal * X :=
    fun ctr acc =>
      let args := ctr.(cstr_args) in
      let fix Ffix l (acc:infolocal * X):=
        match l with
        | [] => acc
        | a :: l' => Ffix l' (visit_arg a acc)
        end
      in
      Ffix (rev args) acc.

  Definition visit_body : one_inductive_body -> infolocal * X -> infolocal * X :=
    fun body acc =>
      let ctrs := body.(ind_ctors) in
      let fix Ffix l e x :=
        match l with
        | [] => (e, x)
        | a :: l' => Ffix l' e (visit_ctr a (e,x)).2
        end
      in
      Ffix ctrs acc.1 acc.2.

  Definition visit_bodies : mutual_inductive_body -> infolocal * X -> infolocal * X :=
    fun ty acc =>
      let bodies := ty.(ind_bodies) in
      let fix Ffix l e x:=
        match l with
        | [] => (e, x)
        | a :: l' => Ffix l' e (visit_body a (e,x)).2
      end
      in
      Ffix bodies acc.1 acc.2.


  (* Definition visit_parameter : context_decl -> infolocal -> X -> X :=
    fun param e acc =>
  Definition visit_bodies : *)

End visit.

Definition and_listbool (l:list bool) (l':list bool) :=
  map2 (fun a b => andb a b) l l'.

(* Print visit_bodies. *)

(* Print visit_body. *)

Axiom print_info : forall {A}, infolocal -> A.

Definition visit_args {X} (kn:kername) (ty:mutual_inductive_body)
  (init:X) (aux:context_decl -> infolocal * X -> infolocal * X): X:=
  let params := ty.(ind_params) in
  let initial_info := make_initial_info kn ty in
  let e :=
    fold_left (fun e param => update_kp param.(decl_name) e (Savelist "params")) params initial_info
  in
  (visit_bodies X aux ty (e, init)).2.

(* Print term. *)

Definition CheckUniformParam (kn:kername) (ty:mutual_inductive_body) : list bool :=
  let npars := length ty.(ind_params) in
  let init := repeat true npars in

  let aux' : context_decl ->  infolocal * list bool -> infolocal * list bool :=
    fun arg '(e, acc) =>

    let fix aux argtype (bl:list bool) e: list bool:=
      match argtype with
      | tLetIn na def def_ty body =>
          let bl' := aux def bl e in
          let e' := update_kp_withbody na e NoSave (Some def) in
          aux body bl' e'
      | tProd na _ t2 | tLambda na _ t2 =>
          aux t2 bl (update_kp na e NoSave )
      | tApp (tRel i) tl =>
        match is_rec_call e i with
        | Ok (Some _) =>
            and_listbool bl
              (mapi (
                fun i t =>
                  match t with
                  |  (tRel k) =>
                      if term_err_eq (Ok $ tRel k) (geti_info "params" e i)
                      then true else false
                  | _ => false end
                ) (firstn npars tl))
        | Ok None => fold_left (fun bl b => aux b bl e) tl bl
        | Error _ => todo
        end
      | tApp t tl =>
        fold_left (fun bl b => aux b bl e) (t::tl) bl
      | _ => bl end
    in

    match arg.(decl_body) with
    | Some body =>
      match normal e body with
      | None => print_info e
      | Some body =>
        let e' := update_kp_withbody arg.(decl_name) e NoSave (Some body) in
        (e', aux body acc e)
      end
    | None =>
      match normal e arg.(decl_type) with
      | None => print_info e
      | Some argtype =>
        (update_kp arg.(decl_name) e NoSave , aux argtype acc e)
      end
    end
  in
  visit_args kn ty init aux'.


(*seperating the list of parameters into "uniform params" and "non-uniform params"*)
(*the function below just find the first non-uniform param and split the list,
  the params after the first non-uniform one are regarded as if they were not uniform        *)
Definition SeperateParams (kn:kername) (ty:mutual_inductive_body) :=
  let findi {X} (f: X -> bool) (l:list X) :option nat :=
    let fix Ffix l n:=
      match l with
      | [] => None
      | y :: l' => if f y then Some n else Ffix l' (n+1)
      end
    in
    Ffix l 0 in
  let params := ty.(ind_params) in
  let bl := CheckUniformParam kn ty in
  match findi (fun b => negb b) bl with
  | None => (params, [])
  | Some i => (skipn (length params - i) params, firstn (length params - i) params)
  end.


(* Load MetaCoqPrelude.

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


Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
  Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.
Definition input_acc:= ($run (tmQuoteInductive (thisfile, "Acc"))).
Compute (CheckUniformParam (thisfile, "Acc") input_acc).

Inductive Acc' (A : Type) (R : A -> A -> Prop) (x : A) : Type :=
  Acc_intro' : (let a := A in forall y : a, R y x -> Acc' A R y) -> Acc' A R x.
Definition input_acc':= ($run (tmQuoteInductive (thisfile, "Acc'"))).
Compute (CheckUniformParam (thisfile, "Acc'") input_acc').


Inductive nu_let1 (A : Type) : Type :=
| nu_let1_nil : nu_let1 A
| nu_let1_cons : let x := A in nu_let1 x -> nu_let1 A.
Definition input_nu_let1 := ($run (tmQuoteInductive (thisfile, "nu_let1"))).
Compute (CheckUniformParam (thisfile, "nu_let1") input_nu_let1).

(* Check nu_let1_ind. *)

Inductive nunest (A B C : Type) : Type :=
| nunest_nil : A -> nunest A B C
| nunest_cons : list (nunest A (B * B) C) -> nunest A B C.
Definition input_nunest := ($run (tmQuoteInductive (thisfile, "nunest"))).
Compute (CheckUniformParam (thisfile, "nunest") input_nunest). *)
