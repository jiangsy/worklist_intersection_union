.PHONY : artifact

UNAME_P := $(shell uname -p)

ifeq ($(UNAME_P),arm )
	SUFFIX := arm64
	BUILD-FLAG := --platform linux/arm64
else 
	SUFFIX := amd64
	BUILD-FLAG := 
endif 

artifact : 
	git clean -dfX
	git clean -df
	cd ./implementation && docker build ${BUILD-FLAG} -t implementation . && docker save implementation:latest | gzip > implementation-$(SUFFIX).tar.gz && mv implementation-$(SUFFIX).tar.gz ../implementation-$(SUFFIX).tar.gz
	cd ./proof && docker build ${BUILD-FLAG} -t proof . && docker save proof:latest | gzip > proof-$(SUFFIX).tar.gz && mv proof-$(SUFFIX).tar.gz ../proof-$(SUFFIX).tar.gz
	zip -r src.zip implementation proof
	zip docker_image_${SUFFIX}.zip implementation-$(SUFFIX).tar.gz proof-$(SUFFIX).tar.gz
	rm implementation-$(SUFFIX).tar.gz
	rm proof-$(SUFFIX).tar.gz