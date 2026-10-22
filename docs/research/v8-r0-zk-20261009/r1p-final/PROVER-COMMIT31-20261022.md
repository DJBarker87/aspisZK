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

## Stage 2 — extraction diagnostics and focused source checks

The owned map loops remove both BTreeMap trait-clause errors. Charon v3 and
subsequent valid lowerings have `has_errors=false`; invalid v1/v2 LLBC is not
accepted evidence. Narrow opaque cuts retain the actual walk, tape, semantic,
opening, encoding, tree-programming and semantic-codec functions and errors.
They are obligations, not successful callbacks or discharged contracts.

Aeneas v3 rejects the native timing addition (`Invalid inputs for binop`).
The reference now retains those exact floating-point operations in opaque
instrumentation helpers. V4 requires the actual SecureCirclePoint ADT, and
v5 the actual R1PublicChallenges ADT; both type declarations are subsequently
included. V6/V7 hit `InterpMatchCtxs.ml:2739` in the mutable opening-cell loop.
Owned lane recursion advances extraction to the byte-publication loop (v8).
The current diagnostic is testing owned recursion for those bytes as well.
No successful Aeneas owner or new Lean theorem is claimed at this stage.

Accepted Kani gates: `publication31-wide_byte-v2` (3.561 s, 429800 KiB peak
RSS) and `publication31-cell_transition-v2` (7.197 s, 427072 KiB). Both exit 0,
zero swaps, with unwinding assertions enabled. The byte gate quantifies over
every canonical eight-limb value and an arbitrary byte position; the cell
gate over arbitrary 4×29 u32 arrays, update and observation coordinates.
The failed whole-array serializer check is an insufficient memcmp unwind
bound, not a serializer counterexample. Its replacement checks an arbitrary
byte without that irrelevant whole-array memcmp loop.

Initial map comparisons were stopped before pressure; whole-map equality,
then recursive BTreeMap clone, inflated the symbolic pointer state. Exact
stopped commands and scope peaks are retained. Changed focused harnesses
construct equal maps from identical inputs and compare selected lookup bytes;
these remain bounded caller checks. Map extensionality remains TrustedStd.
All scopes use 6G high / 8G max / zero swap / 64 tasks. Full commands, source
hashes, dependency fingerprints, exits, times, peaks and swap counts are in
`evidence/prover-commit31-20261022/rust-receipts.jsonl` beside exact source
snapshots. `#print axioms` is N/A for Rust; no Lean attempt has been consumed.
