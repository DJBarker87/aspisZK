# Rewritten ordered query scan continuation

Unmerged adoption candidate on codex/cx-prover-rw-20261023. Continues e46cf2d4b0.
No native code, artifact, backend, launcher, model or trust-boundary changes.
The restored -M7000 rules apply; the existing stricter 5G/7G host launcher is
reused unchanged. All work is in new proof modules.

`ProverRwQueryContains.loop_search` and `contains_exact` prove totality and
finite symbolic refinement of the actual emitted query membership loop for
n≤22. `ProverRwQueryMembership.contains_prefix_iff` identifies its true result
with existence of a matching position strictly below n. There is no dictionary
premise, assumed successful read, or concrete 22-cell reduction.

`ProverRwQueryScan.scan_finite` refines the actual recursive 64-word owner to
structural recursion for draws.val+fuel=64, for arbitrary accepted/n. It keeps
all byte accesses, machine failures/divergence, duplicate checks, updates,
Transcript rejection and selected advance block. `queries_finite` installs the
actual zero-start caller. This is finite source-control refinement, not yet
the model's query policy equation or an adaptive ROM view transport.

Attempts 11306–11310: three passes, two retained elaboration failures, no
resource failures. All nine successful theorem audits use standard axioms only.
The failed 11306 input has an empty revision label because the copied host src
has no Git metadata; exact source snapshot/hash and dependency fingerprint
are retained, actual local base is e46cf2d4b0. Later inputs record that base.
Evidence is under evidence/prover-rw-20261023/query-scan, relative to
 docs/research/100bit-spend-path-20261013/.

The latest retained ledger before this continuation is Lean240/260, Kani59/60,
not the obsolete100/100 checkpoint. Five new Lean compiles give245/260;
no Kani, extraction, Rust, runtime, timing or ELF gate is run. No full manifest
is justified. Next free env-J attempt11311. Original native differential/ELF
receipts remain historical; this step changes no Rust or verifier sources.

Next: connect word decoding and duplicate/fresh transitions to the existing
Q22 mathematical scan, then join the actual transcript materialization and
selected advance state. Full external dictionary, effect-aware entropy/retry
adequacy, remaining per-attempt components, actual PrefixContract/BodyContract,
E1/E2 and joint observer/oracle RunJoin remain open. Conjunct1 and the security
target are not established. Existing theorem premises remain unchanged.
