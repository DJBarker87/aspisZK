# Prover commitment continuation 36

**Target not yet established. Intended trust list: P7, TrustedStd, E1
(successful OS RNG draws), E2 (atomic create-if-absent and persistence).**
The intended endpoint uses the D146 deployed statement image and D143
published-data scope, excluding timing and other side channels. No new
endpoint or removal of RustProverRefinement is claimed.

Actual base: `e91b035a1339e76376ec024ac173418327230462`.
Branch: `codex/cx-prover-commit36-20261022`. No shipped source changed.

## Stage 1: private reservation membership

`R1Z.ProverCommitLedger36` implements private ledger membership. The
adversarial schedule selects faults and added paths using only the call
index, kind and prior statuses. Initial ledger and additions are independent
of the private tape by the strategy interface. Membership is evaluated
privately after additions; occupied paths return AlreadyExists, fresh paths
either fail or are created. Existing entries are retained. A created entry
survives every later write/fsync fault, including directory-open failures.

The model re-proves `fail_closed` and `failure_replay` for the environment
prefix, with arbitrary witness-dependent successful continuations.
`duplicate_path` covers an occupied nonce address; it stops before writes.
These are membership/control model theorems. The module does not claim a
native filesystem instance, byte-content refinement, SHA-256 address law,
or whole simulator/publication theorem. E2 is an explicit named Prop
contract, not a Lean axiom; no native instance has been assumed as proved.

J9128 is a rejected proof draft (a split tactic selected the fault match
instead of ledger membership). J9129 compiles the corrected module: exit 0,
2.09 s, peak RSS 4,164,956 KiB, zero swaps. All eight new theorem audits
use only standard axioms. Exact source snapshots, dependency-object hashes,
commands and raw receipts are under
`evidence/prover-commit36-20261022/lean/`. Each attempt uses its own capped
scope, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean
`-M7000`; no cold dependency build or full regression runs.

## Remaining stages

The requested numerical collision bound is under inspection: the source
uses SHA-256(domain || nonce), rather than the nonce itself, as the filename.
E1 constrains RNG bytes, E2 constrains filesystem transitions, and neither
by itself specifies the distribution of these hashed paths.

Complete native publication, source-to-FSExperiments conversion, concrete
shippedProverExperiment and both WholeRunJoins remain open. The actual
endpoint is unchanged; no premise deletion has occurred.
