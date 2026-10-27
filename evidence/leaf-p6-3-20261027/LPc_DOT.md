# Dot fixed-cell split

K001/K002/K003/K005 check cells0/1/2/3, respectively, with arbitrary canonical
Q operands and arbitrary u64 accumulator cells. Each calls actual Q::raw and
Dot::push. All four time out at90s; none is rerun unchanged. The split still
executes the shared raw producer and its arithmetic safety checks, so it does
not isolate a standalone raw-value-to-sum instruction. This is the exact open
stage, not a counterexample and not closure of canonical operand producers.
K004 fails compilation before any verification (inner doc comment in an
include! file); the harness comment is repaired for K005. Five runs are charged.

Full target/argv/revision/source hashes/exit/wall/RSS/swap/cgroup peak are in
per-run receipt.json. Kani axioms audit is N/A; no Lean result is credited.
Scratch-only patch: frozen computational source remains unchanged. The
incremental LPc patch applies after the inherited LPa_kani_harness.patch.
The additional stage harnesses in the patch are not yet verification results.

No actual-top premise removed/added/changed; before/after and ledger unchanged.
Canonical zero operands and arbitrary sums inhabit the domain. No SAME-witness
joint inhabitant of the top is supplied. Next: three separate claims decoders.
