#!/usr/bin/env bash
# Runs once after the container is created. Non-fatal throughout: a transient
# network hiccup must not block the workspace from opening.
set -u
section() {
	echo "--- $1 ---"
}
warn() {
	echo "WARNING: $*"
}
optional_chown() {
	sudo chown -R ubuntu:ubuntu "$@" 2>/dev/null || true
}
bridge_config_home() {
	local name="$1"
	local source_dir="$2"
	local target_dir="$3"
	section "$name config"
	if [ -z "$source_dir" ] || [ "$source_dir" = "$target_dir" ]; then
		return
	fi
	if [ -e "$target_dir" ] && [ ! -L "$target_dir" ]; then
		warn "$target_dir exists and is not a symlink; leaving as-is"
		return
	fi
	ln -sfn "$source_dir" "$target_dir"
	echo "$target_dir -> $source_dir"
}
show_tool_versions() {
	section "toolchain"
	elan --version || true
	lean --version || true
	lake --version || true
	node --version || true
	claude --version || true
	codex --version || true
	just --version || true
	gh --version | head -1 || true
	glab --version || true
	uv --version || true
}
install_shell_completions() {
	section "shell completions"
	if ! command -v just >/dev/null 2>&1 || ! command -v zsh >/dev/null 2>&1; then
		echo "just or zsh unavailable; skipping just zsh completions"
		return
	fi
	local just_completions
	if just_completions="$(just --completions zsh)" && sudo install -d -m 0755 /usr/local/share/zsh/site-functions && printf '%s\n' "$just_completions" | sudo tee /usr/local/share/zsh/site-functions/_just >/dev/null; then
		echo "just zsh completions installed"
	else
		warn "failed to install just zsh completions"
	fi
}
configure_git_auth() {
	section "git auth"
	mkdir -p "$HOME/.ssh" && chmod 700 "$HOME/.ssh"
	for host in gitlab.semanticallyinvalid.net git.semanticallyinvalid.net; do
		ssh-keyscan -T 5 "$host" 2>/dev/null >>"$HOME/.ssh/known_hosts" || true
	done
	sort -u "$HOME/.ssh/known_hosts" -o "$HOME/.ssh/known_hosts" 2>/dev/null || true
	if [ -S "${SSH_AUTH_SOCK:-}" ] && ssh-add -l >/dev/null 2>&1; then
		echo "ssh agent forwarded ($(ssh-add -l | wc -l) key(s))"
	elif [ -n "${GIT_PAT:-}" ]; then
		git config --global credential.helper store
		printf 'https://oauth2:%s@gitlab.semanticallyinvalid.net\n' "$GIT_PAT" >"$HOME/.git-credentials"
		chmod 600 "$HOME/.git-credentials"
		git config --global url."https://gitlab.semanticallyinvalid.net/".insteadOf "git@git.semanticallyinvalid.net:"
		echo "GIT_PAT credential helper configured (HTTPS)"
	else
		echo "no ssh agent and no GIT_PAT - git push/fetch to the forge will need creds"
	fi
}
install_deepcode_alias() {
	section "deepcode alias"
	for rc in "$HOME/.zshrc" "$HOME/.bashrc"; do
		if grep -q 'alias deepcode=' "$rc" 2>/dev/null; then
			echo "deepcode alias already present in $rc"
			continue
		fi
		cat >>"$rc" <<'DEEPCODE_EOF'

# DeepSeek-backed Claude Code alias
alias deepcode='ANTHROPIC_BASE_URL=https://litellm.semanticallyinvalid.net/ ANTHROPIC_AUTH_TOKEN=${DEEPSEEK_API_TOKEN:-} ANTHROPIC_MODEL=direct/deepseek-v4-pro[1m] ANTHROPIC_DEFAULT_OPUS_MODEL=direct/deepseek-v4-pro[1m] ANTHROPIC_DEFAULT_SONNET_MODEL=direct/deepseek-v4-pro[1m] ANTHROPIC_DEFAULT_HAIKU_MODEL=direct/deepseek-v4-flash[1m] CLAUDE_CODE_SUBAGENT_MODEL=direct/deepseek-v4-pro[1m] ENABLE_TOOL_SEARCH=false /usr/bin/claude "$@"'
DEEPCODE_EOF
		echo "deepcode alias added to $rc"
	done
}
report_lean_toolchain() {
	section "lean toolchain"
	local repo_root pinned
	repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
	pinned="$(cat "$repo_root/lean-toolchain" 2>/dev/null || true)"
	if [ -n "$pinned" ]; then
		echo "pinned: $pinned"
		if ! elan toolchain list 2>/dev/null | grep -qF "${pinned#*:}"; then
			warn "pinned toolchain not baked into the image; elan will download it on first lake run"
		fi
	else
		warn "no lean-toolchain file found"
	fi
	echo "mathlib cache persists at ~/.cache/mathlib (bind mount)"
	echo "note: 'just guarded' needs a systemd user manager, which containers lack;"
	echo "the container itself is capped at 48g (runArgs), so run 'lake build' directly"
}
main() {
	echo "== Arithmetic-Hodge dev container =="
	sudo install -d -o ubuntu -g ubuntu -m 0755 /home/ubuntu/.cache 2>/dev/null || true
	optional_chown /home/ubuntu/.cache/mathlib /home/ubuntu/.cache/uv
	bridge_config_home "claude" "${CLAUDE_CONFIG_DIR:-}" "$HOME/.claude"
	bridge_config_home "codex" "${CODEX_HOME:-}" "$HOME/.codex"
	install_deepcode_alias
	install_shell_completions
	configure_git_auth
	report_lean_toolchain
	show_tool_versions
	echo "== ready: try 'just cache' (fetch Mathlib olean cache) then 'just build' =="
}
main
