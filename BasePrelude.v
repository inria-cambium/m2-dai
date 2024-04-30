Require Export MetaCoqPrelude.
Export MCMonadNotation.
Export List.
Export ListNotations.

Axiom todo : forall {A}, A.

Fixpoint listmake {X:Type} (x:X) (n:Datatypes.nat) :=
  match n with
  | Datatypes.O => []
  | Datatypes.S n => cons x (listmake x n) end.

Definition mkdeclnat a b (n:nat) := mkdecl a b n.

Definition plus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+1)) l.

Definition plus_k_index (l: list (BasicAst.context_decl nat)) k :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)+k)) l.

Definition minus_one_index (l: list (BasicAst.context_decl nat)) :=
  map (fun x => mkdeclnat x.(decl_name) x.(decl_body) (x.(decl_type)-1)) l.

(*
- generalise extrainfo with arbitary information that can be dynamically looked up
- fancy lambda, fancy it lambda, fancy case, fancy app, etc (kind of monadically passing around the extrainfo like state)
- print context
*)

Inductive information : Type :=
| information_list (na : string) (l : list (BasicAst.context_decl nat))
| information_nat (na : string) (n : nat).

Definition lookup_list (l : list information) (na : string) : list (BasicAst.context_decl nat) :=
  match find (fun i => match i with
                      | information_list na' li => String.eqb na na'
                      | information_nat na' n => String.eqb na na'
              end) l  with
    Some (information_list na l) => l
  | _ => []
  end.

Definition lookup_item (l : list information) (na : string) : nat :=
  match find (fun i => match i with
  | information_list na' li => String.eqb na na'
  | information_nat na' n => String.eqb na na'
  end) l  with
  Some (information_nat na n) => n
  | _ => todo
  end.

Fixpoint replace_info (info:list information) (na:string)  (l : list (BasicAst.context_decl nat)) :=
  match info with
  | (information_list s l0) :: info' =>
      if String.eqb s na then (information_list na l) :: info'
      else (information_list s l0) :: (replace_info info' na l)
  | h :: info' => h :: (replace_info info' na l)
  | [] => (information_list na l) :: []
  (* (information_list na l) :: [] *)
  end.

Fixpoint replace_add_info (info:list information) (na:string) (item : BasicAst.context_decl nat) :=
  match info with
  | (information_list s l0) :: info' =>
      if String.eqb s na then (information_list s (item::l0)) :: info'
      else (information_list s l0) :: (replace_add_info info' na item)
  | h :: info' => h :: (replace_add_info info' na item)
  | [] => (information_list na [item]) :: []
  (* (information_list na l) :: [] *)
  end.


Record extrainfo : Type := mkinfo {
  renaming : list (BasicAst.context_decl nat);

  info : list information ;
}.

Definition empty_info := {|
  renaming := [];
  info := [
    (* information_list "params" [];
    information_list "indices" [] *)
  ]
|}.

Definition add_listinfo e na l :=
  mkinfo e.(renaming) ((information_list na l)::e.(info)).

Definition add_T (e:extrainfo) ind_bodies : extrainfo :=
  let ind_names := map (
    fun ind_body => {| binder_name := nNamed (ind_body.(ind_name));
                        binder_relevance := Relevant  |}
    ) ind_bodies in
  let l:= mapi (fun i x => mkdeclnat x None i) ind_names in
  add_listinfo e "rels_of_T" l.

(*for lambda term appear in the type definition*)
Definition update_kp (na:aname) (e:extrainfo) (saveinfo:option string):=
  let item := mkdeclnat na None 0 in
  let renaming :=
    item :: (plus_one_index e.(renaming))
  in
  let info :=
    map (
      fun x => match x with
      | information_list na l => information_list na (plus_one_index l)
      | information_nat na n => information_nat na (1 + n) end
    ) e.(info)
  in
  (* mkinfo renaming info *)
  match saveinfo with
  | None => mkinfo renaming info
  | Some str =>
      mkinfo renaming
        (replace_add_info info str item)
  end
  .

(*for lambda term only appear in the function generated*)
Definition update_mk na (e:extrainfo) (saveinfo:option string) : extrainfo :=
  let renaming := e.(renaming) in
  let info := e.(info) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb na "rels_of_T" then x else
        information_list na (plus_one_index l)
    | information_nat na n => information_nat na (1 + n) end
  ) info in
  let renaming_new := plus_one_index renaming in
  match saveinfo with
  | None =>
      let name := match na.(binder_name) with
        | nAnon => "newvar"
        | nNamed s => s end
      in
      mkinfo renaming_new ((information_nat name 0) :: info_new)
  | Some str =>
      mkinfo renaming_new
        (replace_add_info info_new str (mkdeclnat na None 0))
  end.

(*only used in tCase*)
Definition add_args (e:extrainfo) (ctx: context): extrainfo :=
  let nargs := length ctx in
  let l:= mapi (fun i x => mkdeclnat x.(decl_name) None i) (ctx) in
  (*start with the last argument*)
  let renaming := (tl l) ++ (plus_k_index e.(renaming) (nargs)) in
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb "rels_of_T" na  then
          information_list na (plus_k_index l (nargs-1))
        else
          information_list na (plus_k_index l nargs)
    | information_nat na n => information_nat na (n + nargs) end
    ) e.(info) in
  let arg := information_nat "arg_current" 0 in
  mkinfo (renaming) (arg:: info_new).

Definition fancy_tCase (e:extrainfo) t0 t2 t3 t4 t5 t6 t7 (t8:extrainfo -> list (context * (extrainfo -> term))):term :=
  let pcontext := t5 e in
  let pparams := t4 e in
  (*very limited*)
  let update_pcontext pcontext e :=
    let renaming := e.(renaming) in
    let info := e.(info) in
    let info_new := map (
      fun x => match x with
      | information_list na l => information_list na (plus_k_index l (length pcontext))
      | information_nat na n => information_nat na (n + length pcontext) end
    ) info in
    (*very limited*)
    let l:= mapi (fun i x => mkdeclnat x None (i+1)) (tl pcontext) in
    let renaming_new := plus_k_index renaming (length pcontext) in
    let info_new := (information_list "pcontext_indices" l) :: info_new in
    mkinfo renaming_new info_new
  in
  tCase
    {|
      ci_ind := t0 e ;
      ci_npar := length pparams;
      ci_relevance := t2 e
    |}
  {|
    puinst := t3 e;
    pparams := pparams;
    pcontext := pcontext;
    preturn := t6 (update_pcontext pcontext e)
  |}
  (t7 e)
  (map
    (fun '(c, t) =>
      {| bcontext := map decl_name c;
         bbody := t (add_args e c) |})
    (t8 e)).

Definition update_ctr_arg_back (e:extrainfo) : extrainfo :=
  let info_new := map (
    fun x => match x with
    | information_list na l =>
        if String.eqb "rels_of_T" na then
          information_list na (minus_one_index l)
        else x
    | information_nat na n =>
        if String.eqb "arg_current" na then information_nat na (n + 1)
        else x end
  ) e.(info) in
  mkinfo (tl e.(renaming)) info_new
.

Definition map_with_extrainfo_arg {X Y:Type} (f:X -> extrainfo -> Y) (l:list X)
  (e:extrainfo) :=
  let fix Ffix f l e:=
    match l with
    | x :: l => (f x e) :: (Ffix f l (update_ctr_arg_back e))
    | _ => []
    end
  in
  Ffix f l e.

Axiom print_info: extrainfo -> forall {A}, A .

Definition geti_gen (e:extrainfo) (i:nat) :=
  let l := map (fun x => x.(decl_type)) e.(renaming) in
  tRel (nth i l (print_info e)).

Definition get_id_gen (e:extrainfo) (i:nat) :=
  let l := lookup_list e.(info) "rels_of_id" in
  tRel (nth i l todo).(decl_type).

Definition rels_of (na:string) (e:extrainfo) :=
  let l := lookup_list e.(info) na in
  (**)rev(**) (map (fun x => tRel x.(decl_type)) l).

Definition rel_of (na:string) (e:extrainfo) :=
  let n := lookup_item e.(info) na in
  tRel n.

Definition is_recursive_call_gen (e:extrainfo) i : option nat:=
  let l := map (fun x => x.(decl_type)) (lookup_list e.(info) "rels_of_T") in
  let fix Ffix l j :=
    match l with
    | k :: l0 => if eqb k i then Some j else Ffix l0 (j+1)
      (* if ltb i k then None *)
    | [] => None
  end in
  Ffix l 0.

Definition type_rename_transformer (e:extrainfo) (t:term) : term:=
  let fix Ffix e t :=
    match t with
    | tRel k => geti_gen e k
    | tApp tx tl => tApp (Ffix e tx) (map (Ffix e) tl)
    | tLambda name t1 t2 =>(*tProd ?*) tLambda name (Ffix e t1) (Ffix (update_kp name e None) t2)
    | _ => t (* todo *)
  end in
  Ffix e t.

Definition findi (x:nat) (l:list nat):=
  let fix Ffix x l n:=
    match l with
    | [] => None
    | y :: l' => if eqb y x then Some n else Ffix x l' (n+1)
    end
  in
  Ffix x l 0.

Definition check_return_type (t:term) (e:extrainfo) : option nat :=
  let fix Ffix t e {struct t}:=
    match t with
    | tRel i =>
      let types := lookup_list e.(info) "rels_of_T" in
      let types := map decl_type types in
      findi i types
    | tApp t _ => Ffix t e
    | tProd name _  t2 => Ffix t2 (update_kp name e None)
    | _ => None
    end in
  Ffix t e.


Definition mktProd (saveinfo:option string) na e (t1:extrainfo -> term) (t2:extrainfo -> term) :=
  let e' := update_mk na e saveinfo in
  tProd na (t1 e) (t2 e').

Definition kptProd (saveinfo:option string) na e (t1:extrainfo -> term) (t2:extrainfo -> term) :=
  let e' := update_kp na e saveinfo in
  tProd na (t1 e) (t2 e').

Definition it_kptProd (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
        kptProd saveinfo decl.(decl_name) e (fun e => type_rename_transformer e decl.(decl_type))
          (fun e => Ffix ctx' e t)
  end in
  Ffix ctx e t.

Definition it_mktProd (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let fix Ffix ctx e e0 t:=
    match ctx with
    | [] => t e0
    | decl :: ctx' =>
        let e' := update_kp decl.(decl_name) e saveinfo in
        let e0 := update_mk decl.(decl_name) e0 saveinfo in
        tProd decl.(decl_name) (type_rename_transformer e decl.(decl_type) )
          (Ffix ctx' e' e0 t)
  end in
  Ffix ctx e e t.

Definition mktLambda saveinfo na (e:extrainfo)  (t1:extrainfo -> term)
  (t2:extrainfo -> term)
  : term :=
  tLambda na (t1 e) (t2 (update_mk na e saveinfo)).

Definition kptLambda saveinfo na (e:extrainfo) (t1:extrainfo -> term)
  (t2:extrainfo -> term)
  : term :=
  tLambda na (t1 e) (t2 (update_kp na e saveinfo)).


Definition it_mktLambda (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let fix Ffix ctx e e0 t:=
    match ctx with
    | [] => t e0
    | decl :: ctx' =>
        let e' := update_kp decl.(decl_name) e saveinfo in
        let e0 := update_mk decl.(decl_name) e0 saveinfo in
        tLambda decl.(decl_name) (type_rename_transformer e decl.(decl_type) )
          (Ffix ctx' e' e0 t)
  end in
  Ffix ctx e e t.

Definition it_kptLambda (saveinfo:option string) (ctx:context) (e:extrainfo) (t: extrainfo -> term) : term :=
  let fix Ffix ctx e t:=
    match ctx with
    | [] => t e
    | decl :: ctx' =>
        kptLambda saveinfo decl.(decl_name) e (fun e => type_rename_transformer e decl.(decl_type))
          (fun e => Ffix ctx' e t)
  end in
  Ffix ctx e t.

