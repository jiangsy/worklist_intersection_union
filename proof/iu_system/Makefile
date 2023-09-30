COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile

OTT_FLAGS := -coq_lngen true -signal_parse_errors true

SYSTEMS := uni
IGNORE_DIRS := ""
OTT_OUTS   := $(addsuffix /def_ott.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix /prop_ln.v,${SYSTEMS})

.PHONY: ott lngen coq clean

%/def_ott.v : %/language.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" -i "" $@
	sed -e "/lc_typ[ ](exp_tabs[ ](body_anno/d" -i "" $@ 
	sed -e "/lc_dtyp[ ](dexp_tabs[ ](dbody_anno/d" -i "" $@ 
	sed -e "/lc_a_typ[ ](a_exp_tabs[ ](a_body_anno/d" -i "" $@ 
	sed -e "s/dW/Ω/g" -i "" $@ 

ott : ${OTT_OUTS}

%/prop_ln.v : %/def_ott.v
	lngen --coq $@ --coq-ott $*.ott $*/language.ott
	sed -e "s/.ott./.def_ott./" -i "" $@ 

lngen : ${LNGEN_OUTS}

# a hack to force makefile to detect source file changes
.FILE_LIST : ${LNGEN_OUTS} FORCE
	tree . -if -I ${IGNORE_DIRS} | grep -E "v$$" | cut -c3- | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT} .FILE_LIST ${LNGEN_OUTS}
	tree . -if | grep -E "v$$" | cut -c3- | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

coq : ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

clean :
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm */prop_ln.v */ott_def.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf .FILE_LIST