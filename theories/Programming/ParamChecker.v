Require Import MetaCoq.Programming.BasePrelude.

Definition and_listbool (l:list bool) (l':list bool) :=
  map2 (fun a b => andb a b) l l'.

Definition visit_args {X} (kn:kername) (ty:mutual_inductive_body)
  (init:X) (aux:context_decl->infolocal->X->X): X:=
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
      match is_rec_call e i with
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


(*seperating the list of parameters into "uniform params" and "non-uniform params"*)
(*for inductive principle, "non-uniform parameter" is treated the same way as index (different from uniform)*)
(*the function below just find the first non-uniform param and split the list,
  the params after the first non-uniform one are regarded as if they are not uniform        *)
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

