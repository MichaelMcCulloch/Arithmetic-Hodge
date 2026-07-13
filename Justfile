set positional-arguments

memory_max := "48G"
soft_limit_bytes := "42949672960"
soft_limit_kib := "41943040"

[private]
default:
    @just --list

# Run an additional Lean-related workload.
guarded *command:
    #!/usr/bin/env zsh
    set -u
    if (( $# == 0 )); then
      print -u2 "usage: just guarded <lean-related command> [args...]"
      exit 2
    fi
    if [[ ! -S "${XDG_RUNTIME_DIR:-/run/user/$(id -u)}/bus" ]]; then
      # No systemd user manager (e.g. inside the devcontainer, where the
      # container's own memory limit applies); run unwrapped.
      exec "$@"
    fi
    systemd-run --user --scope --quiet --expand-environment=no \
      -p MemoryMax={{ memory_max }} -- zsh -c '
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
      ' _ "{{ soft_limit_bytes }}" "{{ soft_limit_kib }}" "$@"

# Fetch the Mathlib cache.
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
