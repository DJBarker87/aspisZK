# R69: measured fixed-arity kernel, template-free circle extraction

Base: `265a251ecfbff6cd971a32eccd72cff552786885`.
Selected research execution stage:
`/home/dombarker/project-offloads/aspis-r20-r69-explicit-20260929-b`.

The fixed-arity kernel completes the same two genuine proof fixtures at
**1,495,663 / 1,497,050 CU**, saving **1,714 CU per fixture** against R62.
Both actual 1M-cap runs still exhaust. This is a small performance improvement,
not a solution to the total-budget target.

More importantly, the actual measured source now yields the complete circle-map
call graph without extraction-only normalization or external axiom templates.
It avoids R67/R68's new array-map/chain model dependency. **Successful extraction
and compilation are not a circle-map correctness or privacy proof.**

## Change and checks

Only the guarded-product helper changes in the verifier's execution sources.
The fixed eight limb comparisons, eight widening casts and four final reductions
are written explicitly. The field formulas, partial folds, guard order and
public fallback are retained. Final reductions now occur immediately after
each output expression; tests check the whole returned product. The rest of
the field module, circle source, transcript, protocol, masks, challenges,
commitments and proof layout remain unchanged. No validation was removed.

The staged manifest has 202 pins: the old 197, four frozen reference files and
one differential test. Existing Cargo test-bin metadata is also updated. The
checker verifies the complete delta; it does not infer unchanged source from a
commit message. The original R62 stage is retained, as are prior negative
regressions and the R68 models/evidence.

Executed release/source checks:

- 265,536 canonical QM31 pairs: 65,536 boundary combinations plus 200,000
  pseudorandom pairs, against the frozen R62 public product and independent
  u128 field formula. Prepared multiplication and checked-dot results agree.
- 40 malformed raw-constructor cases, comparing return/panic behavior with the
  frozen source; checked-dot rejection retained.
- Retained ordinary/gather source checks, both genuine host fixtures, and
  3,281 wire controls (3,280 checked rejections and one positive).
- Complete SBF build with overflow checks enabled; no stack-frame overflow
  diagnostic. Same SVM driver, proof hashes, 262,144-byte heap and unchanged
  accounts as R62. Honest diagnostic runs accept; malformed-final diagnostic
  runs reject with Custom(6), not resource failure. At 1M both kinds exhaust;
  those are **not** counted as successful malformed-proof rejections.

ELF SHA-256:
`412c762bb5a0190bd7f068b12fb1323e8ba84985a727b1008fe30f29550dc518`.
No deployment, wallet action, settlement, new fixture or instrumented CU claim.

## Exact extraction and formal boundary

`extract_r69_explicit.py` consumes the newly measured stage byte-for-byte with
the pinned Charon/Aeneas tools, Rust nightly 2026-06-01, checked release arithmetic
and `--include core::option`. `Option::ok_or` now has its extracted Rust body.
There is no eta expansion, no new library replacement and no R68 traversal import.
There are 38 generated functions (zero opaque) and six types. Existing Aeneas
builtins and the compiler/extractor trust boundary still exist; zero external
templates does not mean a verified Rust compiler.

The Lean integration retains all generated declaration bodies exactly, narrowing
only imports to the pinned cache. Four theorems compile:

1. Every pair containing any noncanonical limb returns `ok None` from the guard.
2. Such pairs take the exact existing public fallback computation, retaining
   its Result behavior rather than manufacturing canonical validity.
3. The extracted `Option::ok_or(Some x, e)` returns `Ok x`.
4. The extracted `Option::ok_or(None, e)` returns `Err e`.

Three additional `#print axioms` commands audit the generated product and circle
definition closures. They are audits, **not** three extra correctness theorems.
Dependencies are at most `propext`, `Classical.choice`, `Quot.sound`; no new axiom
or `sorry` is accepted.

The single final focused replay uses R66's 310-object cache and 187 dependency
pins. Per-target command is `lake env lean -j1 -M4500` under a checked cgroup:
MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128.

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| AspisR69Explicit/Types | 0 | 1.19 | 2,525,736 | 0 |
| AspisR69Explicit/Funs | 0 | 1.98 | 2,541,572 | 0 |
| ExplicitGuard | 0 | 1.31 | 2,523,776 | 0 |

Host jobs used requested 5/7 GiB scopes; SBF 12/16 GiB; SVM 5/7 GiB, all
swap-disabled with TasksMax 128. Simultaneous reservations stayed at most 23 GiB.
All recorded child jobs report zero swaps. The final Lean cgroup settings were
read and asserted by its runner. Historical host/SBF/SVM transient units were
already garbage-collected when inspected afterward; their `LoadState=not-found`
default properties are not treated as resource-setting evidence. The command
scopes and time logs, not those missing-unit defaults, establish the recorded
execution context. Host product compilation: 20.55 s / 517,176 KiB peak RSS;
full SBF wrapper: 45.27 s / 599,060 KiB peak RSS.

## Why not continue extending the replacement library?

Four bounded source experiments are retained, all with successful MIR extraction
and translator exit 2 (none accepted as proofs):

- Including chain/`any` exposes the generic `try_fold` associated-type constraint;
  Aeneas rejects it at `SymbolicToPureTypes.ml:1047`.
- Explicitly lifting `Try` associated types does not remove that obstruction.
- Including array bodies exposes an opaque `MaybeDangling` representation.
- Including that representation moves the failure to opaque `ManuallyDrop`.

The fixed-arity runtime candidate removes those operations from this call graph
instead of assuming their semantics or weakening a theorem. The successful
candidate extraction and its SBF measurement are separate from these diagnostic
failures. The earlier extraction-only normalization remains unproved and is not
needed by the new candidate.

## First remaining proposition

For **every canonical pair** `x,y`, prove that the extracted
`AspisR69Explicit.field.r24_canonical_mul x y` returns `ok (some z)`, where `z`
is the canonical encoding of the exact QM31 product. This must establish each
checked multiplication's bounds and the wrapped intermediates' integer/residue
correspondence. Reuse R56's partial-product and R59's width/residue lemmas; do not
introduce a correct-multiplication premise.

Then transport the already-proved R66 inverse to this generated namespace,
compose the complete circle map with its real error order, and prove the bounded
sampler/observer correspondence. Full joint-view, shared-oracle, seed expansion,
semantic messages, failures/retries/publication and numerical privacy-loss
composition remain open. Coherent pre-beta extraction is still a separate
soundness obligation. No full privacy or soundness claim follows from this work.

Audit: `python3 tools/check_r69_evidence.py` from this research directory.
[Receipt](evidence/r69-explicit-source/receipt.json),
[source pins](evidence/r69-explicit-source/SOURCE_PINS.json),
[artifact manifest](evidence/r69-explicit-source/MANIFEST.json).
