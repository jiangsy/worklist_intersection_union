.PHONY : artifact

artifact : 
	rm -r ./doc
	cd ./implementation && docker build -t 35-implementation . && docker save 35-implementation:latest | gzip > implementation.tar.gz
	cd ./proof && docker build -t 35-proof . && docker save 35-proof:latest | gzip > proof.tar.gz
