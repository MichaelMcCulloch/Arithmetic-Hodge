#!/usr/bin/env bash
# Host-side Dev Containers hook. Docker validates bind-mount sources before it
# starts an existing container, so the fixed ssh-agent socket must already exist.
set -euo pipefail
runtime_dir="${XDG_RUNTIME_DIR:-/run/user/$(id -u)}"
socket="$runtime_dir/ssh-agent.socket"
if [ ! -d "$runtime_dir" ]; then
	echo "XDG runtime dir does not exist: $runtime_dir" >&2
	exit 1
fi
agent_is_reachable() {
	local rc
	if SSH_AUTH_SOCK="$socket" ssh-add -l >/dev/null 2>&1; then
		return 0
	fi
	rc=$?
	[ "$rc" -eq 1 ]
}
if [ -S "$socket" ] && agent_is_reachable; then
	exit 0
fi
rm -f "$socket"
eval "$(ssh-agent -a "$socket" -s)" >/dev/null
for key in "$HOME/.ssh/id_ed25519" "$HOME/.ssh/id_rsa"; do
	if [ -r "$key" ]; then
		SSH_AUTH_SOCK="$socket" SSH_ASKPASS_REQUIRE=never ssh-add "$key" </dev/null >/dev/null 2>&1 || true
	fi
done
