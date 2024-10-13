.PHONY : artifact

UNAME_P := $(shell uname -p) # store the output of the command in a variable

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
	cd ./implementation && docker build ${BUILD-FLAG} -t 35-implementation . && docker save 35-implementation:latest | gzip > 35-implementation-$(SUFFIX).tar.gz && mv 35-implementation-$(SUFFIX).tar.gz ../35-implementation-$(SUFFIX).tar.gz
	cd ./proof && docker build ${BUILD-FLAG} -t 35-proof . && docker save 35-proof:latest | gzip > 35-proof-$(SUFFIX).tar.gz && mv 35-proof-$(SUFFIX).tar.gz ../35-proof-$(SUFFIX).tar.gz
	zip -r src.zip implementation proof
	zip docker_image_${SUFFIX}.zip 35-implementation-$(SUFFIX).tar.gz 35-proof-$(SUFFIX).tar.gz
	rm 35-implementation-$(SUFFIX).tar.gz
	rm 35-proof-$(SUFFIX).tar.gz