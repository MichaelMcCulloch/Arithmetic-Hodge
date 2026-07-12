# Justfile Resource Workflow Design

## Goal

Replace the root `Makefile` with one discoverable `Justfile` that keeps routine
project commands concise while enforcing the repository's resource-safety
policy. Agents and humans should use `just` recipes instead of spelling out the
full `systemd-run` invocation.

## Command surface

The root `Justfile` will provide:

- the default recipe, which lists available recipes;
- `just guarded <command...>` for additional Lean-related workloads that can
  grow or run for more than an interactive inspection;
- `just cache` for `lake exe cache get`;
- `just build [target]` for a full or targeted Lake build;
- `just lean <file> [args...]` for direct Lean compilation; and
- `just strict <file> [args...]` for Lean compilation with warnings treated as
  errors.

`cache`, `build`, `lean`, and `strict` will use the guarded path. Non-Lean
commands such as `git`, `rg`, and `git diff` should be run directly; they do
not need or benefit from a systemd scope.

## Resource behavior

Every Lean- or Lake-related recipe-launched workload will run under:

```text
systemd-run --user --scope --quiet --expand-environment=no \
  -p MemoryMax=48G -- <command> <args...>
```

The guarded path will launch the workload in its own process group and poll
both the scope's `memory.current` and the summed RSS of the workload's complete
descendant tree. If either reaches 40 GiB, it will terminate that process group
and return a nonzero status. Normal command exit status will otherwise be
preserved.

## Migration and discovery

The root `Makefile` will be deleted; there will be no compatibility shim.
`GOAL.md` will direct agents to the `Justfile`, document the guarded Lean/Lake
entry points, and prohibit bypassing those recipes for Lean-related work. It
will explicitly permit ordinary non-Lean inspection and version-control
commands to run directly.

## Verification

Validation will cover recipe parsing and listing, argument forwarding, the
cache/build/Lean command previews, a small scoped Lean command, and confirmation
that the Makefile is gone and `GOAL.md` names the new command surface. Expensive
builds are not required to validate the workflow itself.
