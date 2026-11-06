Historical failure record; host repair and one authorized resubmission are complete. NKH_HANDOFF.md and NKH_AUDIT.json now report the final passing composition gate; L025 metrics remain unavailable. L026 is recorded as resubmission after host repair.

# Host-health stop

L025 was submitted once after admission exit0 AND allowed:true, in an8GiB capped scope. The unchanged host launcher failed at S2W_run_host.py:24 while writing receipt.json:

`OSError: [Errno 28] No space left on device`

The local recovery parser then failed on the empty JSON; that parser error is secondary to the host failure. Read-only recovery found0bytes free and empty L025 receipt/stdout/time and proof16 JSON/log/time. No NKH process remained. Child exit, wall, peak RSS, swap and printed axioms are UNKNOWN, not zero or PASS. No scope was resubmitted, cap raised, infrastructure repaired, shared file deleted, or sibling process touched.

Binding local-lean.txt rule5: “Do NOT build or repair build/launcher/monitoring infrastructure. If the launcher or host misbehaves, stop and report the exact error in one paragraph; the lead fixes infrastructure.” Its host-health condition applies here. The user’s script-repair exception covers our own validators, not this launcher/disk fault.

25/40scopes were submitted (62.5%). All remaining15scopes depend on the unavailable coherent host forest and are prohibited by that rule until the lead restores host health. NKH_SCOPE_DISPOSITION.json lists each unlaunched target and every candidate member. NKH_REMAINING.md lists all85OPEN occurrences individually, including future native versus Lean-only work. This is not a Kani-exhaustion stop: the job has0Kani allowance and substantial Lean/audit work remains.

No row or supplement is promoted without the full gate. NKH_LEDGER.json.xz is byte-identical to NKC; counts remain514 CLOSED /0 QUALIFIED /85 OPEN of599. The required all-root audit is incomplete:5367/10066 roots audited,4699missing. Both extra support-root statements, the exact matcher-owner print and final closure pin/export are unrun. All caches and owned host outputs are retained because final export/closure verification could not run; nothing is deleted to repair host infrastructure.

Own validation repairs were retained: exact CHECKPOINT_FIXED expression rather than guessed literal; append two provider-omitted support roots only to the final raw group; inspect historical per-attempt gate snapshots rather than comparing them with a later edited validator; add actual returned-array/PoolTree fidelity controls to the receipt review; import the NJX ledger15 baseline from immutable git into an NKH-prefixed evidence file. These strengthen checks and do not change any formal verdict.
