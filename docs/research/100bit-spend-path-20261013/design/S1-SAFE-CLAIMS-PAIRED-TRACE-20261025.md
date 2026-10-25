# Safe Claims candidate: paired native returned-result and decoder control check

S1/S6 remain OPEN; candidate `891a213f79` remains NOT ADOPTED. This packet
establishes a native value/control comparison under the explicit Kani model.
It does not remove an enclosing SDK theorem premise, establish TOTAL, or
repair the frozen function's failed initialization check.

## Exact paired result

`native_claims::proofs::paired_frozen_safe_claims` executes BOTH complete
function bodies on the SAME Prefix and common symbolic decoder tape:

- Original private Claims body from adopted source freeze
  `25866ec331cc7ce27dd9956609c11d32fa8fa58a`, including actual
  `heap::uninit`, native unsafe row writes and `assume_init`.
- Exact isolated safe-storage body from `891a213f79`, including actual
  `heap::filled(3, [QM31::ZERO;29])`, Vec-to-Box conversion, fallible
  Box-slice-to-array conversion and safe indexed row writes.

Neither allocation helper is stubbed. Imports are factored into small modules;
the original body is unchanged and has one cfg(kani) forwarding wrapper for
its private entry. This is not whole-crate/context/ABI identity. Full frozen
wire and sampler modules and all88 core files are pinned. Two existing wire
proof constructors are appended; no native Error or field carrier is replaced.

The sole stub is `ValidatedRecord::decode_k`. It checks the complete observed
record row25, original frame pointer/length, N29 and call offsets0/29/58, then
supplies the common arbitrary full native return/error tape. Each execution's
call counter is separately reset; both see the same input Prefix and rows.

The paired target checks equality of the COMPLETE returned Rust results:
same Err tag/payload, or all348 returned u32 coordinate words in both native
Boxes. Mixed Ok/Err outcomes fail. It additionally checks equal decoder-call
counts. Together with each decoder-stub invocation's checked arguments and
ordinal, this retains the ordered decoder call prefix, not merely final values.
No independent source/reference success premise or `kani::assume` is used.

All87 raw QM31 cells have all four u32 words symbolic, without a canonicality
restriction. First-error position ranges0/1/2 or no decoder error; every release
WireError variant and payload is covered by the existing any_error generator.
The Prefix has its complete native type, zero root and27 record references to
the same frame; frame length varies0..3717, with zero contents unread by the
stub. This is not an arbitrary-Prefix or arbitrary-decoder-effect transport
proof. Both actual bodies only consume the selected record through their
checked child interface. Child abort/divergence and initialization/drop/oracle
semantics are not inferred from a normal-return tape.

## Allocation and initialization qualifications

Kani's recorded DEFAULT model uses `--no-malloc-may-fail`. Thus the result is
NOT universal allocation-failure equivalence. It is not evidence that the two
programs request the same allocations, have equal allocator states or cleanup,
or preserve all runtime/private-memory effects. Initial zero fills and Box
conversion effects are real candidate work, not erased by the comparison.
The full native Error types remain present, but allocation-error behavior
outside this model is not established by the decoder rejection cases.

`-Z uninit-checks` is absent. The failed original union-pointer checks in
`5c7b15d36b` remain failed. Equality to safe returned values in this DEFAULT
model does NOT establish that the original has no undefined behavior, nor
justify transferring an adaptive-oracle experiment by output equality alone.
This gate supplies only the published candidate value/control comparison;
full source equivalence/adoption still needs the remaining gates below.

## Evidence and measurements

First, the candidate alone passed the same complete returned-value/decoder
characterization already checked for the original in `c6107eb726`. That old
unchanged proof was reused, not replayed. The direct paired check was then run
because the characterization's allocation-error disjunction alone would not
establish pairwise outcome equality. No such inference is used.

The negative paired target changes ONLY the last expected word in the
comparison (row2,column28,c1.b XOR1). It leaves both native function bodies and
all child calls unchanged. It fails exactly at that comparison, confirming the
successful-return comparisons are active. It is excluded from accepted proof
evidence. The checker compares the positive and negative harness texts after
exactly this change and the necessary function renaming.

| Attempt | Target/result | Exit | Wall s | Peak RSS bytes | Sampled aggregate bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| v1 | candidate characterization compile | 0 | 0.686992 | 229883904 | 193675264 | 0 |
| v2 | characterization, 0/839 failed, 3/3 covers | 0 | 19.729845 | 926990336 | 975044608 | 0 |
| v3 | paired target compile | 0 | 0.680156 | 247267328 | 226721792 | 0 |
| v4 | paired target, 0/985 failed, 3/3 covers | 0 | 30.883413 | 1643266048 | 1618526208 | 0 |
| v5 | negative compile | 0 | 0.670248 | 247185408 | 206077952 | 0 |
| v6 | expected negative failure, 1/1001 failed | 1 | 41.704101 | 1749434368 | 1822523392 | 0 |

Targets are respectively `native_claims::proofs::native_claims_full_trace`,
`native_claims::proofs::paired_frozen_safe_claims` and
`native_claims::proofs::paired_frozen_safe_claims_negative_last_word`.

Official Kani0.67.0 aarch64-apple-darwin archive SHA256
`7fd0b71130aa37bd1e346eba675aad09e9b66e4b383f707fc657330ceb29eeec`, rustc
`1.93.0-nightly (53732d5e0 2025-11-20)`. Exact commands, Git revision, actual
source hashes/snapshots, package/tool/host-sysroot pins and pre/post stability
checks are in every input/receipt. Rust optimization and overflow checks are
enabled. Unwind32 with unwinding assertions; no partial loops, resource-option
overrides, custom axioms or native_decide. `#print axioms`: N/A, no new Lean
result. This is a new Mac model check, not an SBF or historical Linux proof.

Each job held the shared atomic compiler lock, with a sampled aggregate2GiB
process-group watchdog,64-process bound and180s timeout. No resource stop or
cap increase. These are ordinary focused Mac checks, not hard cgroups or
MemorySwapMax enforcement; measured process swaps are zero. No SSH, NUC,
Aeneas, cold dependency build, full manifest or release-runtime replay ran.

A fresh source-only97-file kit exactly reconstructs all selected final source
hashes, including the original forwarding wrapper and candidate body. The
preparer records immutable Git origins and full-body/span hashes. It performs
no compiler/solver execution. The kit is local preparation, not adoption or
host permission. Earlier proof versions are kept as their original snapshots:
v1/v2 precede the pair, v3/v4 precede the negative control. They are not silently
relabeled as the final maintained source. All six snapshots contain the correct
selected root and their contemporaneous hashes.

Source-only focused-extractor-proof-packet-v1 audit:

```
python3 tools/s1-safe-claims-trace-20261025/check.py
```

It passes95 source/evidence hashes, original/candidate Git body bindings, all
receipts/tool/source stability, exact positive targets, successful counters and
the excluded negative control. No binaries are distributed. No production
source, protocol, caller, release artifact or other owner's worktree changed.

## Exact remaining obligations

This closes the candidate's normal-return value/decoder-control comparison
gate under the stated default allocation model. It does not close the broader
native equivalence or source-adoption gate. Still required:

1. Actual allocation-failure behavior, allocation/layout/state and drop/cleanup/
   private-effect correspondence, or a separately justified replacement
   refinement sufficient for the accepted security event.
2. Candidate extraction and ordinary kernel checks with concrete reachable
   library children and caller installation. The97-source extraction plan and
   disabled source-only release remain unexecuted pending fresh reviewed host
   admission; this Mac Kani packet does not authorize them.
3. Cost/stack/two-transaction validation and explicit source/artifact/affected
   parent re-pins before any adoption decision.
4. Existing arithmetic/Std/native hash/oracle-effect, semantic Claims/Terminal,
   coherent original/current environment and shared enclosing caller/release
   joins. The accepted Claims range result stays at its `cef39d839d` scope.

The frozen unsafe Claims initializedness proof remains OPEN. The safe candidate
is an isolated available route, not a silently changed verifier. S2 remains
transferred; the shared S6/kernel/release join stays lead-owned. Both whole
S1/S6 and the <=2^-100 per-attempt target remain not yet established.
