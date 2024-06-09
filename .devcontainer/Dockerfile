FROM mcr.microsoft.com/devcontainers/base:jammy

# [Optional] Uncomment this section to install additional packages.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install clang gcc zlib1g-dev python3-pip file libtool libncursesw5-dev autotools-dev autoconf automake build-essential texinfo libidn2-dev

RUN for file in /usr/bin/llvm-*-14; do fname=$(basename "$file"); ln -s $file /usr/local/bin/${fname%-14}; done

# RUN curl https://sh.rustup.rs -sSf | sh -s -- -y

RUN pip3 install wllvm benchexec coloredlogs

ENV LLVM_COMPILER=clang