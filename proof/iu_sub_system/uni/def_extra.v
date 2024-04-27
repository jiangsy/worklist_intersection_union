Require Import uni.def_ott.

Inductive work : Set := 
 | work_infer (e:exp) (c:typ -> work)
 | work_check (e:exp) (A:typ)
 | work_infabs (A:typ) (c:typ -> work)
 | work_infapp (A:typ) (e:exp) (c:typ -> work)
 | work_inftapp (A1:typ) (A2:typ) (c:typ -> work)
 | work_sub (A1:typ) (A2:typ)
 | work_apply (c:typ -> work) (A:typ).
