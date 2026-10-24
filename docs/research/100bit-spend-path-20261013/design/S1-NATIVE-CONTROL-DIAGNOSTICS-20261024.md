# Original claim control diagnostics — 2026-10-24

**No original-native-claim equivalence or totality result is established by
these experiments.** Retain the unchanged target and use the failures to select
the next proof approach. No production source, frozen artifact or tool binary
was modified.

## Original extraction, alternate MIR stages

`evidence/s126-current-caller-20261021/s1-native-mir-20261024` retains the exact
source kit, runners, admission/command/receipt logs and hashes of valid LLBC
(no LLBC or binaries distributed). Promoted, elaborated and optimized Charon
runs all exit zero (0.336, 0.340, 0.366 seconds); each corresponding Aeneas
translation exits 2 (0.342, 0.368, 0.368 seconds). All have zero swap.

These alternate MIR stages preserve the original claim source and still hit
the interpreter's reduction/collapse context failure. They do not supply a
Lean source evaluator for the original claim. Neither a skipped borrow replay
nor a suppressed assertion is accepted as a repair.

## Whole-function Kani and loop-contract isolation

`evidence/s126-current-caller-20261021/s1-loop-contract-20261024` is a
source-only packet containing full inputs and excluded outcomes:

| Attempt | Outcome | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|
| whole original/reference with common powers cut | timeout, exit 1 | 182.729 | 6,393,168 | 0 |
| tiny range contract, original syntax | compile failure | 0.144 | 92,988 | 0 |
| tiny range contract, corrected syntax | verified, 142 checks | 0.517 | 110,752 | 0 |
| original/reference loop contract v1 | integer inference compile failure | 0.216 | 143,872 | 0 |
| original/reference loop contract v2 | Kani compiler panic | 0.244 | 160,272 | 0 |
| v2 diagnostic with backtrace | same compiler panic | 0.263 | 169,636 | 0 |
| inner-only loop contract v3 | same compiler panic | 0.227 | 159,164 | 0 |
| tiny early-return contract, insufficient invariant | failed check | 0.539 | 129,452 | 0 |
| tiny early-return contract, count ≤ stop added | verified | 0.541 | 129,612 | 0 |
| unchanged original/reference, ordered result tapes | timeout, exit 1 | 181.581 | 2,085,752 | 0 |

The corrected syntax requires `stmt_expr_attributes`, `proc_macro_hygiene`
and `kani::index` (a macro pseudo-variable, without parentheses). Original
inferred `usize` ranges must be explicitly suffixed in the annotated candidate
because the Kani iterator transformation otherwise defaults the detached
expression to `i32`. These type annotations preserve the original inferred
range types; they are recorded rather than called byte-identical source.

The tiny early-return failure was a missing inductive invariant, not a tool
counterexample to Rust semantics. The corrected invariant records the absence
of an earlier stop. It passes, so ordinary early returns alone do not explain
the whole-claim compiler panic. The retained full backtrace identifies
`LoopContractPass::transform_body_with_loop` calling `MutableBody::insert_bb`
after a terminator without a `target` field. Reducing to only the inner loop
annotation did not remove this failure. No compiler patch is used or trusted.

The ordered-tape experiment avoids the previous recursively nested UF
expressions. Its source `prepared_claim` body agrees with the frozen
`b2727acd3abf79315d18b754a260f58f4b1c6326` body modulo whitespace; the complete
input lib is byte-identical to the retained parent input. All 174 push result
states, six finish results, 29 field results, seven products/sums and powers
are shared arbitrary tapes. Each source leaf call asserts its complete ordered
arguments, and a symbolic first rejection ordinal covers every normal-return
prefix. No success/canonicality/output restriction is assumed. Nevertheless,
the whole check timed out. It supplies no claim-equivalence credit. Even a
successful such check would still need association with concrete arithmetic
and transport of panic/abort/runtime effects.

Every substantive Kani run records fresh application and global admission,
`-j1`, optimized Rust flags, explicit MemoryHigh/MemoryMax and
MemorySwapMax=0. Whole jobs used 6/8 GiB; tiny capability checks used 1/2 GiB.
Time was expected in compilation followed by CBMC control checking, without
native field evaluation. The backtrace rerun was solely to collect the missing
compiler diagnostic, not to retry an unchanged proof at higher resource limits.

## Provenance qualifications

Raw capped receipts retain the host checkout's historical `source_revision`
`d8fc9db732c70ef8dd1dd548184326318d5e1ad1`; this is **not** the source identity
of the submitted kit. Exact input/source/tool/Cargo.lock hashes in each
`input.json`, the complete before/after local dependency inventories and the
frozen source-body comparison identify the inputs. The inherited whole-powers
runner description mistakenly says `from_fn`; its actual command, harness and
source identify the whole claim. Parent binding JSON files in copied candidate
crates remain historical evidence and do not override new proof hashes.

Audit with `python3 tools/s1-claim-powers-cut-20261024/check-diagnostics.py`.
The packets contain only sources, text logs, JSON and hashes, not binaries.

Next native deliverable remains the original-to-owned whole claim connection.
The existing checked one-step and Lean loop-induction results must be composed
through an actual original-source execution boundary; a standalone loop model
or independently successful reference is not a substitute. The whole-claim
checks above must not be repeated unchanged with more memory or time.
