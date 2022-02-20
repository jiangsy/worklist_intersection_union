
- binding of tvar and extvar
- 

- usage of formula
- why reduction on G not wl
- what does dwork mean  
    dwork, w :: 'dw_' ::=
  | ob |= e1 <: e2 <= A :: :: check
  | e1 <: e2  => x . wl :: :: infer (+ bind x in wl +)
  | A . e => x . wl :: :: infer_app (+ bind x in wl +)
  | e --> x . wl :: :: reduce (+ bind x in wl +)
  | A <~: B      :: :: compact

- generate test cases
- finish ott defns 
- add new rule to fix soundness
