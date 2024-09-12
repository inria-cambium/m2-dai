Require Import MetaCoq.Programming.
Global Open Scope bs.


Definition add_emp_info e saveinfo :=
  match saveinfo with
  | Some str =>
    mkinfo e.(renaming) ((str, []) :: e.(info)) e.(info_source) e.(kn)
  | _ => e end.


Definition it_kptProd_default (saveinfo:option string) (e:infolocal) (ctx:context) (t: infolocal -> term) : term :=
  let e := add_emp_info e saveinfo in
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
          Ffix ctx' e (
            fun e =>
              kptProd saveinfo e decl.(decl_name)
                (mapt e decl.(decl_type)) t
          )
    end in
  Ffix ctx e t.


Definition it_mktProd_default' (saveinfo:option string) (e:infolocal) (ctx:context)
  (t: infolocal -> infolocal -> term) : term :=
  let e := add_emp_info e saveinfo in
  let saveinfo :=
    match saveinfo with | None => NoSave | Some str => Savelist str
  end in
  let fix Ffix ctx e e0 t:=
    match ctx with
    | [] => t e e0
    | decl :: ctx' =>
        Ffix ctx' e e0 (fun e e0 =>
          let e' := update_kp decl.(decl_name) e saveinfo in
          let e0 := update_mk decl.(decl_name) e0 saveinfo in
          tProd decl.(decl_name)
            (mapt e decl.(decl_type))
            (t e' e0)
        )
    end in
  Ffix ctx e e t.


Definition it_mktProd_default (saveinfo:option string) (e:infolocal) (ctx:context)
  (t: infolocal -> term) : term :=
  it_mktProd_default' saveinfo e ctx (fun _ => t).


Fixpoint Ffix_findi (l:list nat) (j:nat) (i:nat) :=
  match l with
  | k :: l0 => if eqb k i then Some j else Ffix_findi l0 (j+1) i
  | [] => None
  end.


Definition is_rec_call (e:infolocal) i : option nat:=
  let l := rev_map (fun x => x.(decl_type)) (lookup_list e.(info_source) "rels_of_T") in
  Ffix_findi l 0 i.
