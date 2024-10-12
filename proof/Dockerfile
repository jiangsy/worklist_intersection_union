FROM coqorg/coq:8.15.2

ENV LC_ALL=C.UTF-8

USER root

RUN sudo apt-get update -y && \
    sudo apt-get install -y --no-install-recommends \
        tree \
        curl \
        libnuma-dev \
        zlib1g-dev \
        libgmp-dev \
        libgmp10 \
        git \
        wget \
        lsb-release \
        software-properties-common \
        gnupg2 \
        apt-transport-https \
        gcc \
        autoconf \
        automake \
        build-essential \
        pkg-config \
        libgmp-dev

# install ghcup
RUN curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup > /usr/bin/ghcup && \
    chmod +x /usr/bin/ghcup

ARG GHC=8.10.7
ARG CABAL=latest

# install GHC and cabal
RUN ghcup -v install ghc --isolate /usr/local --force ${GHC} && \
    ghcup -v install cabal --isolate /usr/local/bin --force ${CABAL}

USER coq

RUN cd /home/coq && \
    git clone https://github.com/plclub/metalib && \
    cd metalib && git -c advice.detachedHead=false checkout badeeab && \
    cd Metalib && make install

RUN cd /home/coq && \
    git clone https://github.com/sweirich/ott.git && \
    cd ott && git -c advice.detachedHead=false checkout aa65f53 && make

RUN cd /home/coq && \
    git clone https://github.com/plclub/lngen.git && \
    cd lngen && git -c advice.detachedHead=false checkout 67b9acc && \
    cabal update && cabal install --lib syb && cabal new-build

USER root

RUN cp /home/coq/ott/bin/ott /usr/bin/ott && \
    ln -s /home/coq/lngen/dist-newstyle/build/x86_64-linux/ghc-${GHC}/lngen-0.3.2/x/lngen/build/lngen/lngen /usr/bin/lngen

USER coq

COPY --chown=coq:coq . /proofs
WORKDIR /proofs