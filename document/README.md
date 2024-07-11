
```
Inductive information : Type :=
  | information_list (l : list (BasicAst.context_decl nat))
  | information_nat (n : nat).

Record infolocal : Type := mkinfo {
  renaming : list (BasicAst.context_decl term);
  info : list (string * information) ;
  info_source: list (string * information) ;
  kn : kername;
}.
```

```
Definition geti_info (na:string) (e:infolocal) (i:nat): term

(*
  get the tRel term of the ith element of the information list named [na] inside [e.(info)].


  i.e.
    if (information_list na l) is in e.(info),
    then the result is:  tRel (nth i (rev_map decl_type l) todo)

  remark:
    the "rev" may be strange here, but is reasonable
    but since all elements of l is added by the user, the element added at last
    in the list is in fact at the head of the list (it works in this way),
    So here (geti_info na e i) in fact gets the ith element we added into the l.
*)
```

```
Definition rels_of (na:string) (e:infolocal) :list term

(*
  get the reversal (tRel term) list of the information list named [na] of [e]

  i.e.
    if (information_list na l) is in e.(info),
    then the result is: rev_map (fun decl => tRel decl.(decl_type)) l
*)
```


```
Definition rel_of (na:string) (e:infolocal) :term.

(*
  get the tRel term of the informationitem named [na] of [e]

  i.e.
    if (infomation_nat na i) is in e.(info),
    then the result if (tRel i)
*)
```

```
Definition mapt (e:infolocal) (t:term) : term.

(*
  transform the term in the source to the corresponding term in the target.

  i.e.
    we simply regard e.(renaming) as a (list term),

    then (mapt e t) will recursively substitute each subterm of t,
    base case is : mapt e (tRel i) = nth i e.(renaming) todo.

*)
```


```
Definition is_rec_call (e:infolocal) i : option nat.

(*
  check if [tRel i] refers to an inductive body,
  if it refers to the kth inductive body, then return (Some k)

  e.x.
    Inductive ntree (A:Set) : Set :=
      nnode : A -> nforest A -> ntree A
                   ^^^^^^^
    with nforest (A:Set) : Set := ...

    the noted "nforest" in the MetaCoq representation is (tRel 2).
    if (is_rec_call e 2) is called in that stage (while the e is always updated correctly)
    then it will return (Some 0), meaning that it refers to the last inductive body.
*)
```


```
Definition kptbind (saveinfo:saveinfo) (e:infolocal) (na:aname) (t1:term) (t2:infolocal -> term) :term.

Definition mktbind (saveinfo:saveinfo) (e:infolocal) (na:aname) (t1:term) (t2:infolocal -> term) :term.
(*
  build the term [tbind na t (t2 _)] (tbind is tLambda or tProd)
  [saveinfo] indicates if the binder will be saved in the e.(info)

  these two functions differ in how the [e] will be updated.
*)
```


```
Definition it_kptbind (saveinfo:option string) (e:infolocal) (tp:infolocal -> term -> term)
  (ctx:context) (t: infolocal -> term) : term.

(*
  currently, only used to iteratively bind the list of parameters,
  assume ctx is [uk:tyk ; ...; u1:ty1] the result looks like:
    tbind u1 (tp _ ty1) (tbind u2 (tp _ ty2) ... (tbind uk (tp _ tyk) (t _ ) ...))

  where [tp] is a function to transform the type in the source to the type in the target
*)

Definition it_mktbind (saveinfo:option string) (e:infolocal) (tp:infolocal -> term -> term)
  (ctx:context) (t: infolocal -> term) : term.

(*
  currently, only used to iteratively bind the list of indices
*)

(* the default version of these two functions above by defining (tp := mapt) *)
Definition it_kptbind_default (saveinfo:option string) (e:infolocal)
  (ctx:context) (t: infolocal -> term) : term.
Definition it_mktbind_default (saveinfo:option string) (e:infolocal)
  (ctx:context) (t: infolocal -> term) : term.
```

