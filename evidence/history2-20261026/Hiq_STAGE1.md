# Stage 1: account and history collision accounting

Ledger delta: none yet. L094–L098, L159, L180 remain open.

Before: RawJ_CollisionBudget.replay_collision charges Q0+Q1+2961 for the whole
adaptive account source and canonical replay. Hist_ByteExperiment separately
requires an associated fixed-before-H program with a uniform first-read bound.

After: Hiq_AccountAudit.queries/collision use the SAME GExq_AccountExperiment
program with RawJ_AccountBudget, then canonical replay and four complete-byte
audit reads in that order. One bad event has bound 6*(Q0+Q1+2965)^2/2^256.
No extra independent history collision summand is charged. Selection is still
an arbitrary pure function of the source outcome; source association is next.

Hiq_Numeric.exact_zero_margin proves the requested original margin minus
6*(2965^2-2961^2)/2^256; margin_positive proves it remains strictly positive.
This is arithmetic/accounting, not an installed security endpoint.

Retained: uniform preprocessing Q0 and adaptive-choice Q1 envelopes, source
and SDK/extraction/runtime/child trust, and unresolved runtime classification
and same-key/source-output association. No new trust, source, feature, wire,
parameter or ELF changes. Pins inherited from Hist_/RawJ_, not rebuilt.

Validation: Hiq_001 and 002, two focused host compiles, both exit0, standard
axioms only. Exact target, command, revision anchor with dirty source snapshots,
source/dependency/tool hashes, wall, peak RSS, swap and cgroup readings in each
receipt. Reused coherent SInt2 objects; no package replay, Rust or Kani.
Budget used 2/100 Lean, 0/20 Kani. No kill, timeout or cap increase.
