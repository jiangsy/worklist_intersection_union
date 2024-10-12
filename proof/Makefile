COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile

OTT_FLAGS := -coq_lngen true -signal_parse_errors true

SYSTEMS := uni uni_rec uni_monoiu systemf
IGNORE_DIRS := ""
OTT_OUTS   := $(addsuffix /def_ott.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix /prop_ln.v,${SYSTEMS})

ifeq ($(OS), Windows_NT)
	UNAME_S := Windows
else
	UNAME_S := $(shell uname -s)
endif

ifeq ($(UNAME_S), Darwin)
	SED_FLAG := -i ""
else
	SED_FLAG := -i
endif

.PHONY: ott lngen coq coq-only clean clean-coq-only

%/def_ott.v : %/language.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" ${SED_FLAG} $@
	sed -e "s/dW/Ω/g" ${SED_FLAG} $@ 
	sed -e "s/aW/Γ/g" ${SED_FLAG} $@ 
	sed -e "s/dE/Ψ/g" ${SED_FLAG} $@
	sed -e "s/aE/Σ/g" ${SED_FLAG} $@ 
	sed -e "s/fE/Δ/g" ${SED_FLAG} $@ 

ott : ${OTT_OUTS}

%/prop_ln.v : %/def_ott.v
	lngen --coq $@ --coq-ott $*.ott $*/language.ott
	sed -e "s/.ott./.def_ott./" ${SED_FLAG} $@ 
	sed -f ./scripts/$*_prop_ln.sed ${SED_FLAG} $@ || true

lngen : ${LNGEN_OUTS}

# a hack to force makefile to detect source file changes
# .FILE_LIST : ${LNGEN_OUTS} FORCE
# 	tree . -if -I ${IGNORE_DIRS} | grep -E "v$$" | cut -c3- | sort -s > .FILE_LIST.tmp
# 	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
# 	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT}  .FILE_LIST
	tree . -if | grep -E "v$$" | cut -c3- | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

coq : ${LNGEN_OUTS} ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

coq-only : ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

clean-coq-only : 
	${MAKE} -f ${COQ_MAKEFILE} clean

clean : clean-coq
	rm */prop_ln.v */def_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf
