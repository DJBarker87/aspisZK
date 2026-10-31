#!/bin/sh
# codex-run.sh <worktree> <prompt-file> <out-file>: lead-driven Codex job (gpt-6.1-sol, medium). Run via Bash run_in_background so the lead is notified at exit.
set -u
WT=$1; P=$2; OUT=$3
cd "$WT" || exit 66
codex exec --dangerously-bypass-approvals-and-sandbox -m gpt-6.1-sol -c model_reasoning_effort=\"medium\" -C "$WT" "$(cat "$P")" > "$OUT" 2>&1
echo "codex-exit=$?" >> "$OUT"
