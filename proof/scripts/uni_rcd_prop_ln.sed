/^Lemma size_work_open_work_wrt_typ_rec_mutual/,/^Qed.$/ {
  s/default_simp/default_simp; auto 6 with arith lngen/
}