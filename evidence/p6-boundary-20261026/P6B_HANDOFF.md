# P6B final handoff

Target not yet established. Branch codex/cx-p6-boundary-20261026.

The exact missing law is `forall parts, exists digest, hashv parts = ok digest`.
P6B_Totality.installed_total_iff proves this is necessary AND sufficient for
the total installed op43 law under D188, RuntimeSyscall and P1. Its wrapper
counterpart and nonvacuity are kernel-checked. This is a runtime return/abort
obligation beyond the adopted success-only RuntimeSyscall. No new trust is
adopted. The job's explicit runtime-trust stop condition takes precedence
over spending the remaining compile/Kani budget on unrelated work.

Before/after: identical complete Rc3_Top source snapshots accompany this
report. No quantifier/carrier/failure event/conclusion changed. Ledger recount:
actual82T+113P unchanged; deployment6T+13P unchanged; aliases4P unchanged;
deduplicated88T+126P unchanged. Delta ZERO. L166,L195–L199 remain P/lead/
deployment-only. Op5T already proves the four ideal program gates; it does
not remove their actual deployed source/log association. L166 also retains
independent global SDK carrier/rejected-prefix/source effects obligations.
No new mathematical gate theorem is promoted to deployment closure.

Non-vacuity is scoped precisely: existing P1 and RuntimeSyscall admit a
partial oracle with a successful empty-parts query and a nonreturning nonempty
query. This refutes implication to totality; it is not evidence of a shipped
execution or full deployment antecedent satisfiability.

Validation: P6B_002 exit0,5.847740322s,4362528KiB peakRSS,swap0; six standard
axioms audits. P6B_001 local simp failure excluded.2/100 Lean,0/20 Kani.
Existing coherent SInt2 cache/runner reused, no dependency/package replay.
Exact commands/revisions/source/dependency hashes/caps are in receipts.
One reservation refusal was retried after3minutes; no bypass or cap change.

Next concrete deliverable for the lead: determine whether a return/abort law
on a justified runtime admission domain is already approved, or replace the
all-input boundary with a proved accepted-run transport accounting for
rejected oracle prefixes. Do not silently add blanket VM totality.

Only P6B source and receipt files changed. No shipped/cfg(kani) source changed;
no ELF rebuild trigger. Inherited pins, NOT reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No keys, sibling candidates or session A worktrees touched. No push.
