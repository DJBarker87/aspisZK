# Prover commitment continuation 31 — publication owner

Source base: b5e845cb4 (inherited LOG D141). Branch:
`codex/cx-prover-commit31-20261022`. Work in progress; target not established.

The native walk evidence from part 30 is reused. The next interface is the
ordered publication/retry owner, retaining the real tape/semantic/opening
contracts, then entropy/reservation, observable conversion and both run joins.
No refinement premise is removed by introducing an owned reference.

## Stage 1 — owned publication reference

Added cfg(kani)/cfg(aeneas_ref) `sim::owned31`: ordered consuming map snapshots,
conflict-retaining insertion, first-conflict merge, capped node publication,
and a copy of the actual simulator owner using these transitions. Production
control flow is unchanged. Validation and frozen ELF rebuild pending.

BTreeMap stays TrustedStd: total lexicographic ordering of byte-vector keys and
numeric ordering of usize keys; unique keys; insert returns the prior value
and installs the new value; clone preserves entries; pop_first removes exactly
the minimum key; iter/into_iter visit each entry once in the same increasing
order; get/index return the unique value; len is entry count. No hash or
cryptographic property follows from these standard-library laws.
