FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
RUN source ~/.profile
RUN lake exe cache get!
RUN lake build BrownCs22

ENV PATH="/home/vscode/.elan/bin:/workspaces/CS22-Lean-2024/scripts:${PATH}"
