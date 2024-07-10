(* Require Import MetaCoq.ScopedProgramming.cterm.
Require Import MetaCoq.ScopedProgramming.cinfo.
Require Import MetaCoq.ScopedProgramming.cbody.
Require Import MetaCoq.ScopedProgramming.cterm_generation.


Definition kpcProd {n k nind:nat} {l} (saveinfo:saveinfo) na (e:cinfo n k nind l)
  (t1:cterm n) (t2 : cinfo (S n) (S k) nind (replace_info_len saveinfo l)-> cterm (S n))
  : cterm n
  := kpcProd saveinfo na e t1 t2.

Definition mkcProd {n k nind:nat} {l} (saveinfo:saveinfo) na (e:cinfo n k nind l)
  (t1:cterm n) (t2:cinfo (S n) k nind (replace_info_len saveinfo l) -> cterm (S n))
  : cterm n
  := mkcProd saveinfo na e t1 t2.

Definition is_rec_call {n m nind l} (e:cinfo n m nind l) (i:nat)
  : option ({i:nat | i < nind})
  := is_rec_call e i.

Definition mapt {n m nind:nat} {l} (e:cinfo n m nind l) (t:cterm m)
  : cterm n
  := mapt e t.

Definition it_kpcProd {n k m nind:nat} {l} (saveinfo:saveinfo)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: forall (e:cinfo (n + m) (k + m) nind (addl l saveinfo m)) ,
    cterm (n + m))
  : cterm n
  := it_kpcProd saveinfo ctx e t.

Definition it_mkcProd {n k nind m:nat} {l} (saveinfo:string)
  (ctx:context_closed k m) (e:cinfo n k nind l)
  (t: cinfo (n + m) (k + m) nind (addl' l saveinfo m)-> cterm (n + m))
  : cterm n
  := it_mkcProd saveinfo ctx e t.

Definition make_initial_cinfo (kn:kername)
  (ty:mutual_inductive_body_closed)
  (h:wf_ind_closed ty)
  :cinfo 0 ty.(nind') ty.(nind') []
  := make_initial_cinfo kn ty h.



Definition rel_of {n k nind:nat} {l} (na:string) (e:cinfo n k nind l)
  : cterm n
  := rel_of na e.

Definition rels_of {n k nind:nat} {l} (na:string) (e:cinfo n k nind l)
  : list (cterm n)
  := rels_of na e.

Definition geti_info {n k nind l} (na:string) (e:cinfo n k nind l) (i:nat)
  (h:within_info e na i)
  :cterm n
  := geti_info na e i h. *)




