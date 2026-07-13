# Arithmetic-Hodge dev container

A reproducible Lean 4 / Mathlib proof environment, mirroring the libcans
devcontainer layout (minus CUDA/Rust, which this project does not use).

| Component | Version | Path |
| --- | --- | --- |
| Lean (elan) | `leanprover/lean4:v4.29.0-rc8` (pinned from `lean-toolchain`) | `/usr/local/elan` |
| Node | 22 | system |
| claude-code / codex | pinned in Dockerfile `ARG`s | npm global |
| just, glab, gh, yq, shfmt, uv | pinned in Dockerfile `ARG`s | `/usr/local/bin` |

Base image: `ubuntu:24.04`.

## Host prerequisites

- Docker (BuildKit — any recent version)
- An ssh key at `~/.ssh/id_ed25519` or `~/.ssh/id_rsa` for the forge;
  `.devcontainer/ensure-ssh-agent.sh` starts/loads a host agent at
  `$XDG_RUNTIME_DIR/ssh-agent.socket` before the container starts and it is
  bind-mounted at `/ssh-agent`.
- Persistent caches live on the host under
  `~/ContainerData/DevContainers/Arithmetic-Hodge/{mathlib-cache,uv}` —
  the Mathlib olean cache (`lake exe cache get`) survives container rebuilds.
- `~/.claude`, `~/.codex`, and `~/.config/glab-cli` are bind-mounted so agent
  CLIs and glab reuse host auth/config.

## First run

```sh
just cache    # fetch the Mathlib olean cache (fast after the first time — bind-mounted)
just build    # build the project
```

## Caveats vs the host

- The Lean toolchain is baked into the image at `/usr/local/elan` (world
  writable, like libcans' rustup layout). If `lean-toolchain` is bumped, elan
  downloads the new toolchain into the running container; bump the
  `LEAN_TOOLCHAIN` build `ARG` and rebuild to re-bake it.
- `DEEPSEEK_API_TOKEN` is forwarded from the host environment for the
  `deepcode` alias (added to `.zshrc`/`.bashrc` by `postCreate.sh`).
- Git auth: prefers the forwarded ssh agent; falls back to a `GIT_PAT` env var
  (HTTPS credential helper for `gitlab.semanticallyinvalid.net`).
