FROM mcr.microsoft.com/devcontainers/base:jammy

# [Optional] Uncomment this section to install additional packages.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && sudo apt-get -y install clang gcc zlib1g-dev python3-pip file

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y

RUN pip3 install wllvm

ENV LLVM_COMPILER=clang