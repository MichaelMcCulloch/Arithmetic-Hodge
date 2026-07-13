# syntax=docker/dockerfile:1.7

# Lean 4 / Mathlib proof environment — no GPU, no Rust toolchain needed.
FROM ubuntu:24.04

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

# Keep downloaded .debs in BuildKit's apt cache mount instead of deleting them
# after every apt invocation. The cache is not committed into the final image.
RUN rm -f /etc/apt/apt.conf.d/docker-clean \
    && echo 'Binary::apt::APT::Keep-Downloaded-Packages "true";' \
        > /etc/apt/apt.conf.d/keep-cache \
    && echo 'Acquire::Languages "none";' > /etc/apt/apt.conf.d/no-translations \
    && echo 'force-unsafe-io' > /etc/dpkg/dpkg.cfg.d/docker-unsafe-io \
    && install -d -m 0755 /etc/apt/keyrings

# Build/runtime dependencies in one apt transaction. The Justfile's `guarded`
# recipe runs zsh scripts through systemd-run/setsid/ps/awk, so those tools are
# baked in even though systemd-run --user needs a user manager (see README).
ADD --chmod=0644 https://grml.org/zsh/zshrc /tmp/grml-zshrc
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt/lists,sharing=locked \
    set -eux; \
    apt-get update; \
    apt-get install -y --no-install-recommends \
        bat build-essential ca-certificates curl direnv dnsutils entr \
        fd-find file fzf gawk gh git gnupg iproute2 iputils-ping jq \
        less lsb-release lsof netcat-openbsd openssh-client \
        pkg-config procps pv python3 python3-venv ripgrep shellcheck \
        sqlite3 strace sudo systemd unzip util-linux wget xz-utils zsh zstd; \
    ln -sf /usr/bin/batcat /usr/local/bin/bat; \
    ln -sf /usr/bin/fdfind /usr/local/bin/fd; \
    install -m 0644 /tmp/grml-zshrc /etc/skel/.zshrc; \
    install -o ubuntu -g ubuntu -m 0644 /tmp/grml-zshrc /home/ubuntu/.zshrc; \
    rm -f /tmp/grml-zshrc; \
    chsh -s /usr/bin/zsh ubuntu; \
    gh --version | head -1; \
    rg --version | head -1; \
    fd --version; \
    bat --version; \
    systemd-run --version | head -1

# elan + the project's pinned Lean toolchain (mirrors ./lean-toolchain), shared
# system-wide so the ubuntu user can still add toolchains later.
ENV ELAN_HOME=/usr/local/elan
ENV PATH=/usr/local/elan/bin:${PATH}
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.29.0-rc8
RUN set -eux; \
    curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain "${LEAN_TOOLCHAIN}"; \
    chmod -R a+w "$ELAN_HOME"; \
    lean --version; \
    lake --version

# Node 22 from the official dist tarball (the NodeSource apt repo proved
# unreliable from inside the build), then the agent CLIs (pinned) and uv.
ARG NODE_VERSION=22.23.1
RUN --mount=type=cache,id=arithmetic-hodge-dl-node,target=/var/cache/buildkit,sharing=locked \
    set -eux; \
    f="/var/cache/buildkit/node-v${NODE_VERSION}-linux-x64.tar.xz"; \
    [ -s "$f" ] || curl --retry 5 --retry-all-errors --connect-timeout 10 -fsSL \
        "https://nodejs.org/dist/v${NODE_VERSION}/node-v${NODE_VERSION}-linux-x64.tar.xz" -o "$f"; \
    tar -xJf "$f" -C /usr/local --strip-components=1 --exclude='*/CHANGELOG.md' --exclude='*/README.md' --exclude='*/LICENSE'; \
    node --version | grep -F "v${NODE_VERSION}"; \
    npm --version

ARG CLAUDE_VERSION=2.1.207
ARG CODEX_VERSION=0.144.3
RUN --mount=type=cache,target=/root/.npm,sharing=locked \
    set -eux; \
    npm install -g @anthropic-ai/claude-code@${CLAUDE_VERSION} @openai/codex@${CODEX_VERSION}; \
    curl -LsSf https://astral.sh/uv/install.sh -o /tmp/uv-install.sh; \
    env UV_INSTALL_DIR=/usr/local/bin sh /tmp/uv-install.sh; \
    rm -f /tmp/uv-install.sh; \
    claude --version; \
    codex --version; \
    uv --version

# Prebuilt CLI tooling — one layer per tool so bumping one version rebuilds only
# that tool. Each download lands in a per-tool BuildKit cache mount keyed by the
# versioned filename, so a layer rebuild re-fetches only the changed artifact.
RUN --mount=type=cache,id=arithmetic-hodge-dl-yq,target=/var/cache/buildkit,sharing=locked \
    set -eux; \
    f=/var/cache/buildkit/yq_linux_amd64; \
    [ -s "$f" ] || curl --retry 5 --retry-all-errors --connect-timeout 10 -fsSL \
        https://github.com/mikefarah/yq/releases/latest/download/yq_linux_amd64 -o "$f"; \
    install -m 0755 "$f" /usr/local/bin/yq; \
    yq --version

ARG SHFMT_VERSION=v3.10.0
RUN --mount=type=cache,id=arithmetic-hodge-dl-shfmt,target=/var/cache/buildkit,sharing=locked \
    set -eux; \
    f="/var/cache/buildkit/shfmt_${SHFMT_VERSION}_linux_amd64"; \
    [ -s "$f" ] || curl --retry 5 --retry-all-errors --connect-timeout 10 -fsSL \
        "https://github.com/mvdan/sh/releases/download/${SHFMT_VERSION}/shfmt_${SHFMT_VERSION}_linux_amd64" -o "$f"; \
    install -m 0755 "$f" /usr/local/bin/shfmt; \
    shfmt --version

ARG GLAB_VERSION=1.102.0
RUN --mount=type=cache,id=arithmetic-hodge-dl-glab,target=/var/cache/buildkit,sharing=locked \
    set -eux; \
    f="/var/cache/buildkit/glab_${GLAB_VERSION}_linux_amd64.tar.gz"; \
    [ -s "$f" ] || curl --retry 5 --retry-all-errors --connect-timeout 10 -fsSL \
        "https://gitlab.com/gitlab-org/cli/-/releases/v${GLAB_VERSION}/downloads/glab_${GLAB_VERSION}_linux_amd64.tar.gz" -o "$f"; \
    tar -xzf "$f" -C /tmp bin/glab; \
    install -m 0755 /tmp/bin/glab /usr/local/bin/glab; \
    rm -rf /tmp/bin; \
    glab --version

ARG JUST_VERSION=1.53.0
RUN --mount=type=cache,id=arithmetic-hodge-dl-just,target=/var/cache/buildkit,sharing=locked \
    set -eux; \
    f="/var/cache/buildkit/just-${JUST_VERSION}-x86_64-unknown-linux-musl.tar.gz"; \
    [ -s "$f" ] || curl --retry 5 --retry-all-errors --connect-timeout 10 -fsSL \
        "https://github.com/casey/just/releases/download/${JUST_VERSION}/just-${JUST_VERSION}-x86_64-unknown-linux-musl.tar.gz" -o "$f"; \
    tar -xzf "$f" -C /tmp just; \
    install -m 0755 /tmp/just /usr/local/bin/just; \
    rm -f /tmp/just; \
    just --version

# Passwordless sudo for the default user
RUN echo 'ubuntu ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/ubuntu \
    && chmod 0440 /etc/sudoers.d/ubuntu

# Run as the non-root default user
USER ubuntu
