# Justfile Resource Workflows Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the Makefile with a discoverable Justfile that safely scopes and guards Lean/Lake workloads while leaving ordinary shell tools unscoped.

**Architecture:** The Justfile exposes first-class Lake and Lean recipes plus one generic Lean-workload guard. The guard enters the exact 48 GiB user scope, launches the workload in a separate process group, and stops it if either cgroup memory or summed descendant RSS reaches 40 GiB. `GOAL.md` becomes the agent-facing discovery point and explicitly distinguishes Lean-related commands from ordinary `git`, `rg`, and diff operations.

**Tech Stack:** just 1.56, zsh, systemd user scopes, procfs/cgroup v2, Lean 4/Lake.

## Global Constraints

- Systemd scoping is only required for Lean- or Lake-related workloads.
- Every scoped workload uses exactly `systemd-run --user --scope --quiet --expand-environment=no -p MemoryMax=48G --`.
- Guarded workloads stop at 40 GiB by either cgroup `memory.current` or summed descendant RSS.
- Ordinary `git`, `rg`, and diff commands run directly without systemd.
- Delete the root `Makefile`; do not add a compatibility shim.
- Preserve every unrelated tracked and untracked workspace file.

---

### Task 1: Replace Make with scoped Just workflows

**Files:**
- Create: `Justfile`
- Delete: `Makefile`
- Modify: `GOAL.md:184-224`

**Interfaces:**
- Consumes: systemd user scopes, cgroup v2 `memory.current`, `ps`, `awk`, `setsid`, Lake, and Lean.
- Produces: `just guarded`, `just cache`, `just build`, `just lean`, and `just strict`.

- [ ] **Step 1: Verify the old workflow fails the new acceptance checks**

Run:

```bash
just --list
test ! -e Makefile
rg -n 'just (guarded|cache|build|lean|strict)' GOAL.md
```

Expected: `just --list` reports that no Justfile exists, `test ! -e Makefile`
fails because the Makefile still exists, and the `rg` command finds no new
agent-facing recipe documentation.

- [ ] **Step 2: Add the minimal Justfile implementation**

Create `Justfile` with exactly this command surface and guard:

```just
set positional-arguments := true

memory_max := "48G"
soft_limit_bytes := "42949672960"
soft_limit_kib := "41943040"

[private]
default:
    @just --list

# Run an additional Lean-related workload inside the guarded 48 GiB scope.
guarded *command:
    #!/usr/bin/env zsh
    set -u
    if (( $# == 0 )); then
      print -u2 "usage: just guarded <lean-related command> [args...]"
      exit 2
    fi
    systemd-run --user --scope --quiet --expand-environment=no \
      -p MemoryMax={{memory_max}} -- zsh -c '
        set -u
        soft_limit_bytes="$1"
        soft_limit_kib="$2"
        shift 2

        setsid -- "$@" &
        job=$!
        cgroup_rel=$(cut -d: -f3 /proc/$$/cgroup)
        cgroup="/sys/fs/cgroup${cgroup_rel}"

        terminate_job() {
          kill -TERM -- "-$job" 2>/dev/null || true
        }
        trap '"'"'terminate_job; exit 130'"'"' INT
        trap '"'"'terminate_job; exit 143'"'"' TERM HUP

        if [[ ! -r "$cgroup/memory.current" ]]; then
          print -u2 "resource guard: cannot read $cgroup/memory.current"
          terminate_job
          wait "$job" 2>/dev/null || true
          exit 125
        fi

        while kill -0 "$job" 2>/dev/null; do
          memory_current=$(<"$cgroup/memory.current")
          rss_kib=$(ps -eo pid=,ppid=,rss= | awk -v root="$job" '"'"'
            {
              parent[$1] = $2
              rss[$1] = $3
              pids[++count] = $1
            }
            END {
              keep[root] = 1
              for (pass = 1; pass <= count; pass++)
                for (i = 1; i <= count; i++)
                  if (keep[parent[pids[i]]])
                    keep[pids[i]] = 1
              for (pid in keep)
                total += rss[pid]
              print total + 0
            }
          '"'"')

          if (( memory_current >= soft_limit_bytes || rss_kib >= soft_limit_kib )); then
            print -u2 "resource guard: stopping pid $job (cgroup=${memory_current}B rss=${rss_kib}KiB)"
            terminate_job
            sleep 1
            kill -KILL -- "-$job" 2>/dev/null || true
            wait "$job" 2>/dev/null || true
            exit 137
          fi
          sleep 1
        done

        wait "$job"
      ' _ "{{soft_limit_bytes}}" "{{soft_limit_kib}}" "$@"

# Fetch the Mathlib cache under the Lean workload guard.
cache:
    @just guarded lake exe cache get

# Build the whole project, or one optional Lake target.
build target="":
    #!/usr/bin/env zsh
    if [[ -n "$1" ]]; then
      exec just guarded lake build "$1"
    fi
    exec just guarded lake build

# Compile one Lean file; additional Lean flags follow the file argument.
lean file *args:
    #!/usr/bin/env zsh
    exec just guarded lake env lean "${@:2}" "$1"

# Compile one Lean file with warnings treated as errors.
strict file *args:
    #!/usr/bin/env zsh
    exec just guarded lake env lean -DwarningAsError=true "${@:2}" "$1"
```

- [ ] **Step 3: Remove the Makefile and document discovery in GOAL.md**

Delete `Makefile`. Replace the resource-safety opening in `GOAL.md` with text
that names the new recipes and preserves the exact policy:

```markdown
Lean- and Lake-related workloads must use the root `Justfile`; do not spell out
or bypass its systemd wrapper:

```text
just cache
just build [target]
just lean <file> [lean-args...]
just strict <file> [lean-args...]
just guarded <other-lean-related-command> [args...]
```

These recipes run the workload in a transient user systemd scope capped at
exactly 48 GiB. The guarded runner also terminates the workload's complete
process group if either cgroup memory or summed descendant RSS reaches 40 GiB.
Ordinary non-Lean commands such as `git`, `rg`, and `git diff` run directly;
they do not need a systemd scope.
```

Adjust the following bullets so “never unscoped” and subagent propagation
apply to Lean/Lake workloads only. Retain the aggregate-memory warning and the
rule that reaching the cap is a design failure.

- [ ] **Step 4: Verify recipe parsing and argument forwarding**

Run:

```bash
just --fmt --check
just --list
just --dry-run cache
just --dry-run build
just --dry-run build ArithmeticHodge.Analysis.ShiftedLegendreL2Basis
just --dry-run lean ArithmeticHodge/Analysis/ShiftedLegendreL2Basis.lean
just --dry-run strict ArithmeticHodge/Analysis/ShiftedLegendreL2Basis.lean -Dpp.universes=true
just --dry-run guarded lake env lean --version
```

Expected: formatting succeeds; the five public recipes are listed; every
Lean/Lake preview reaches `guarded`; file, target, and flag arguments appear in
the correct order; the scope includes the exact `MemoryMax=48G` property and
both 40 GiB monitor thresholds.

- [ ] **Step 5: Run a small real scoped Lean command**

Run:

```bash
just guarded lake env lean --version
```

Expected: exits zero and prints the installed Lean version. The command runs
inside a transient user scope and does not start a project build.

- [ ] **Step 6: Verify migration and workspace hygiene**

Run:

```bash
test -f Justfile
test ! -e Makefile
rg -n 'just (guarded|cache|build|lean|strict)|git.*rg.*diff' GOAL.md
git diff --check
git status --short
```

Expected: the Justfile exists, the Makefile is absent, GOAL.md documents both
the scoped Lean recipes and direct non-Lean commands, diff checking succeeds,
and status shows only `Justfile`, `Makefile`, `GOAL.md`, plus pre-existing
unrelated files.

- [ ] **Step 7: Commit only the workflow files**

```bash
git add -- Justfile Makefile GOAL.md
git commit -m "replace Make with guarded Just workflows"
```

Expected: one commit containing only the Justfile creation, Makefile deletion,
and GOAL.md policy update.
