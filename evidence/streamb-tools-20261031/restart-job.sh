#!/bin/bash
# restart-job.sh <job> <worktree-name> <base-prompt-file>: stop the Codex session bound to the worktree (by PID), keep its output, relaunch with a resume prompt
S=/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad; j=$1; w=/Users/dominic/ZK/.worktrees/$2; base=$3
for p in $(ps -A -o pid,command | grep -E "codex exec .* -C $w( |$)" | grep -v grep | awk '{print $1}'); do pp=$(ps -o ppid= -p $p); kill $p $pp 2>/dev/null; done
pkill -f "codex-retry.sh $w " 2>/dev/null; sleep 3
left=$(ps -A -o command | grep -E "codex exec .* -C $w( |$)" | grep -v grep | wc -l | tr -d ' '); [ "$left" != 0 ] && { echo "STILL RUNNING in $w"; exit 1; }
n=1; while [ -e $S/prompt-pv-$j-s$n.txt ]; do n=$((n+1)); done; r=pv-$j-s$n
for f in $S/codex-pv-$j.out*; do [ -e "$f" ] && mv "$f" $S/held/$(basename $f).stall$n; done
cat > $S/prompt-$r.txt <<EOP
Read $base and obey it in full (same worktree, branch, ID ranges, budget, receipts directory, rules).
RESUME after a model-service stall (session $n). The lead stopped the previous session by PID; you are the ONLY writer. FIRST: git status; verify and commit uncommitted receipts and evidence; derive spent IDs and attempts from on-disk and host receipts (never reuse an ID); wait for, and collect, any host scope the stopped session left live (never duplicate it). Then continue from where it stopped within the remaining budget. If you are near the end of your context, commit HANDOFF.md. Final answer as in the original prompt.
EOP
( $S/codex-retry.sh $w $S/prompt-$r.txt $S/codex-$r.out > /dev/null 2>&1 & ); echo "relaunched $r"
