left. inst_cofinites_for a_wl_red__sub_arrow1; auto. intros.
               clear IHme. clear IHmj. clear IHmt. clear IHmtj. clear IHma. clear IHmaj. 
               clear IHms. clear IHmev. clear IHmw.
               apply aworklist_subst_rename_tvar with (X1:=X1) (Y:=X0) in Hsubst as Hsubstrn1.
               simpl in Hsubstrn1. destruct_eq_atom.
               rewrite subst_typ_in_typ_fresh_eq in Hsubstrn1; auto.
               rewrite subst_typ_in_typ_fresh_eq in Hsubstrn1; auto.
               rewrite <- rename_tvar_in_aworklist_app in Hsubstrn1. simpl in Hsubstrn1.
               destruct_eq_atom.
               rewrite ftvar_in_aworklist'_awl_app in Fr. simpl in Fr.
               rewrite rename_tvar_in_aworklist_fresh_eq in Hsubstrn1; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Hsubstrn1; auto.
               apply aworklist_subst_rename_tvar with (X1:=X2) (Y:=X3) in Hsubstrn1 as Hsubstrn2.
               simpl in Hsubstrn2. destruct_eq_atom.
               rewrite subst_typ_in_typ_fresh_eq in Hsubstrn2; auto.
               rewrite subst_typ_in_typ_fresh_eq in Hsubstrn2; auto.
               rewrite <- rename_tvar_in_aworklist_app in Hsubstrn2. simpl in Hsubstrn2.
               destruct_eq_atom.
               rewrite ftvar_in_aworklist'_awl_app in Fr0. simpl in Fr0.
               rewrite rename_tvar_in_aworklist_fresh_eq in Hsubstrn2; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Hsubstrn2; auto.
               eapply aworklist_subst_det with (Γ1:=Γ0) in Hsubstrn2; eauto.
               destruct_conj. subst.
               simpl. destruct_eq_atom.
               econstructor.
               apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X0) in JgArr1 as Jgrn1; simpl; auto.
               simpl in Jgrn1.
               rewrite <- rename_tvar_in_aworklist_app in Jgrn1. simpl in Jgrn1.
               destruct_eq_atom.
               rewrite subst_typ_in_typ_subst_typ_in_typ in Jgrn1; auto.
               rewrite subst_typ_in_typ_subst_typ_in_typ with (A1:=A2) in Jgrn1; auto.
               rewrite subst_typ_in_awl_rename_neq_tvar in Jgrn1; auto.
               simpl in Jgrn1. destruct_eq_atom.
               rewrite subst_typ_in_typ_fresh_eq with (A2:=A1) in Jgrn1; auto.
               rewrite subst_typ_in_typ_fresh_eq with (A2:=A2) in Jgrn1; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Jgrn1; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Jgrn1; auto.
               apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X2) (Y:=X3) in Jgrn1 as Jgrn2; simpl; auto.
               simpl in Jgrn2.
               rewrite <- rename_tvar_in_aworklist_app in Jgrn2. simpl in Jgrn2.
               destruct_eq_atom.
               rewrite subst_typ_in_typ_subst_typ_in_typ in Jgrn2; auto.
               rewrite subst_typ_in_typ_subst_typ_in_typ with (A1:=A2) in Jgrn2; auto.
               rewrite subst_typ_in_awl_rename_neq_tvar in Jgrn2; auto.
               simpl in Jgrn2. destruct_eq_atom.
               rewrite subst_typ_in_typ_fresh_eq with (A2:=A1) in Jgrn2; auto.
               rewrite subst_typ_in_typ_fresh_eq with (A2:=A2) in Jgrn2; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Jgrn2; auto.
               rewrite rename_tvar_in_aworklist_fresh_eq in Jgrn2; auto.
               --- admit.
               --- simpl. rewrite aworklist_subst_dom_upper with (Γ:=work_sub ` X (typ_arrow A1 A2)
               ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1). simpl.  fsetdec.
