#!/bin/bash
# usage: codex-retry.sh <worktree> <prompt> <out>
# Durable copy (2026-10-31): macOS /tmp cleanup deleted the scratchpad original.
# Before each run it restores the shared rule files into the scratchpad, where briefs reference them.
# Runs codex-run.sh; on "model at capacity" it WIP-commits, waits 60 s and relaunches with a RESUME note, up to 8 times.
# The final out file ends with exactly one codex-exit= line.
I=$HOME/aspis-lead-infra
S=/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad
W=$1; P=$2; O=$3; n=0
mkdir -p "$S"; for f in local-lean.txt r1p-common.txt codex-run.sh; do [ -f "$I/$f" ] && cp -p "$I/$f" "$S/$f"; done
while :; do
  "$I/codex-run.sh" "$W" "$P" "$O.run$n" ;
  if grep -q 'at capacity' "$O.run$n" && [ $n -lt 8 ]; then
    git -C "$W" add -A . >/dev/null 2>&1; git -C "$W" commit -q -m "WIP snapshot before capacity relaunch (auto $n)" >/dev/null 2>&1
    R="$P.resume$n"; { echo "RESUME AFTER CAPACITY ERROR (automatic relaunch $((n+1))): you are continuing your own interrupted run in this worktree. Your commits plus a WIP snapshot hold all prior work; read your own receipts/handoff, count the attempts already used against the budget below, then continue."; cat "$P"; } > "$R"; P=$R
    n=$((n+1)); sleep 60; continue
  fi
  cat "$O".run* > "$O" 2>/dev/null; grep -v '^codex-exit=' "$O" > "$O.tmp"; tail -1 "$O.run$n" | grep '^codex-exit=' >> "$O.tmp" || echo "codex-exit=1" >> "$O.tmp"; mv "$O.tmp" "$O"; break
done
