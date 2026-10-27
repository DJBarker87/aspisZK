# D300 / D188 mutable-state fidelity audit

Base: `b3d109c8ffa47e452b57c5e4a7fe71cfb98e7146`. Branch:
`codex/pv-d188-20261027`. Worktree:
`/Users/dominic/ZK/.worktrees/pv-d188` (unchanged).
**Target not yet established. No endpoint premise is removed.**

The raw release-kit `low_base_p_digits` attribution is **WITHDRAWN**: its
inherited Lean measurements disagree with freshly executed frozen native
function text on P, P+1 and all-ff. Its zero case agrees. The checked indexed
Stream B copies agree with native on those four cases. No new divergence was
found in a selected Stream B emission tested here. Unchecked native
composition remains **SUSPENDED**, not silently credited from a model theorem.

## Inventory and scope

[INVENTORY.md](INVENTORY.md) and [inventory.json](inventory.json) contain **449
emitted or source-annotated module candidates**, including 316 with Aeneas's
generated-file header, 338 direct PV/ProverRw root-family files, and 4,917
embedded Rust function/type/trait source attributions. The inventory deliberately
includes hand ports and old reference cohorts rather than mistaking them for
fresh shipped-body extractions. Each entry retains its SHA256 and the function
name, Rust path and source span it claims to translate. `lib.rs`, `owned.rs` and
other probe-relative paths denote reference/wrapper sources; they do not alone
identify a shipped function. [ROWS.md](ROWS.md) supplies the operation/ledger
association and preserves that distinction.

The scanner starts with all 2,831 PV/ProverRw source files at the exact base
(including evidence-owned private Lean cohorts) and follows imports to 3,963
candidate files. [import-edges.json](import-edges.json) records the graph. EJR's
`selected[].resolution` is used where present, consistent with ruling (h').
Seventeen remaining multi-source module names are retained as explicit
alternatives; 214 unresolved imports are recorded, predominantly external
Lean/Mathlib/Aeneas libraries plus a few unavailable local adapters. This is a
conservative source-review envelope, **not a newly certified release import
manifest**. No arbitrary variant was installed and no shared source was written.

The older P2 document at this base does not yet contain P3. Its later finding
and SDX measurements were read with `git show research:<path>`.
[reused-evidence.json](reused-evidence.json) pins the exact research revision,
blob and SHA256; [SDX_FINDING.reused.md](SDX_FINDING.reused.md) preserves the
reused evidence. It is not represented as a fresh raw-kit replay.

## Static scan and writeback inspection

[paired-static-matches.json](paired-static-matches.json) associates every lexical
emission match with its embedded Rust source span and current Rust write/borrow
sites in that span. [rust-mutable-sites.json](rust-mutable-sites.json) also lists
whole-file current Rust sites, because an old emitted line pin can predate the
current source. [static-matches.json](static-matches.json) retains all 1,737
matches, including safe callbacks and lexical noise such as `fallback`.

The scan includes `iter_mut`, `chunks_mut`, `chunks_exact_mut`, `get_mut`,
`index_mut`, `next_back`, backward/restoration names, discarded tuple components,
and functional Array/Slice/Vec updates. Source-side matches include dereference
assignments, indexed assignments and mutable arguments. [MUTABLE-DECLARATIONS.md](MUTABLE-DECLARATIONS.md)
lists 423 declaration occurrences in the envelope with both locations.
[PRIMARY-MUTABLE.md](PRIMARY-MUTABLE.md) isolates 92 declarations in 24 direct
PV/ProverRw mutation-bearing files. These counts include helper bodies and
multiple cohorts, not 423 distinct native functions or 423 bugs.
[function-dispositions.json](function-dispositions.json) records per-declaration
dispositions: 41 inspected/tested helper occurrences retain their local credit;
382 unverified historical, reference or dictionary-dependent occurrences remain
suspended. These occurrence counts are not ledger row counts.

Important inspected shapes:

- `PV_CB_Op72Funs.lean:36,44,62,68`: the range-restoration functions are applied
  to the modified slices; the resulting whole slice is carried into the next
  write and ultimately returned. Native field writes are `field.rs:425–426`
  and `:1029–1030`.
- `ProverRwSampler/Funs.lean:39,85,123`, `PV_OrdinarySource.lean:22,72,113`,
  and the drop-free sampler's `Funs.lean:131,167,241` carry the arrays produced
  by `Array.update`. The quotient is a value supplied to the update, not an
  ignored division. Native sampler writes include `sampler.rs:14,26,36,63,93`.
- `PV_B1_254_Funs.lean:332` binds `(_, index_mut_back)` and calls
  `index_mut_back p` on both branches. The underscore is the old element,
  **not** the restoration function. Native `prover_powers.rs:9` stores `p`.
- `PV_CB_Op118Funs.lean:284,325,328` retains the successor and absorption
  updates. Native `state_only_prefix.rs:606,610,611` writes those elements.
- Tuple and forest `tuple_cells_loop.body` functions carry `limbs1` after
  each Array update. Native tuple writes are `pair_trace.rs:1031` and
  `pair_forest_trace.rs:505` (exact matching source text is retained).
- The Full prover's direct index updates and slice callbacks are exposed in
  the review queue. Five closed helpers were tested separately. That does not
  establish the remaining arbitrary callback dictionaries or native effects.
- V195's native `WideExact::to_le_bytes` uses `chunks_exact_mut`
  (`wide_exact.rs:275–276`), but its credited emission is the flat
  `wide_bytes_flat` reference (`PV_CB3_Op51Source.lean:15`), which constructs
  the complete byte array. Its original/native association is the retained
  no-stub `kani-wide-flat-001` gate; this audit ran no Kani and credits no raw
  mutable-chunk emission for that body.

A named backward variable occurring in a returned closure is not unused.
Discarding an old element before overwriting it, an ordinary product projection,
or an immutable FnOnce capture is not by itself P3. Conversely, no source row
is cleared merely because its theorem compiles or the scan found no underscore.

## Raw P3 family and actual Stream B reliance

Raw emission locations below are in the **research-pinned raw release kit**
`evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean`
(SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`),
not a newly imported source in this branch.

| Function | Raw emission / frozen Rust write | D188 disposition | Stream B reliance at this base |
|---|---|---|---|
| `sampler::low_base_p_digits` | declaration 3599, dropped fourth callback 3624 / `sampler.rs:61–63` | WITHDRAWN | V256/V257 would require a legitimate source association; CB3 staged, OrdinarySource and R2 indexed references do not call this raw body. The selected op248 QM31 sampler uses its own indexed division. |
| `sampler::add_small_base_p` | body 3475, next 3484, wrapper 3519/3524 / `sampler.rs:90–96` | SUSPENDED for raw body | V256 gamma requires this operation's semantics, but its inspected indexed references use Array.update; fresh carry/one tests agree. No raw-body credit restored. |
| `multiproof::verify_in_place` | nested body 1154/1174, body 1277, iter_mut 1353 / `multiproof.rs:174–176` | SUSPENDED | No definition/call of this raw body found in the audited Stream B source-law closure. V254's `binary_parent` is a distinct helper, not this verifier. |
| `verifier::update_residue_row` | body 1960/1968, wrapper 1994/2009 / `verifier.rs:235–243` | SUSPENDED | No direct consumed emission found. No Stream B source row can be closed for this body by the present packet. |
| `verifier::BatchedWeights::finish` | body 6348/6365, wrapper 6398/6402 / `verifier.rs:226` | SUSPENDED | No direct consumed emission found. V259/V260 concern `weights::Weights` constructor/raw references, which are different functions. |

The four raw suspended bodies have no admitted unchanged executable environment
here: the raw kit has the retained Iterator/FnMut/from_fn elaboration failures
and external templates. No axiom template, invented opaque implementation or
worker ABI repair was supplied to make a test pass.

Batch 2 is **not in b3d109c8ff** and was not merged. A read-only inspection of its
committed sibling revision is pinned in [batch2-readonly-observation.json](batch2-readonly-observation.json).
Its `host_sampler.rs:3–31` uses indexed quotient/digit writes and `:40–51` uses
indexed carry writes; ordinary/gamma call those local helpers. It routes around
the original sampler's iterator bodies. This observation grants no new batch-2
proof credit and does not substitute its later emission for a base-branch module.

## Differential evidence

[differential.json](differential.json) contains the exact compared projections,
inputs identified by the retained test sources, results, Lean IDs and native
run IDs. Every success used a case where a write changes a later read. Tests are
measurements, never proof terms. Raw payloads, Result wrappers, quotient/carry
outputs and errors are retained in `*-out.log`.

| Function / tested route | Inputs | Result |
|---|---|---|
| Raw XRn low digits (inherited emission result; fresh native baseline) | zero, P, P+1, all-ff | zero agrees; other three DISAGREE |
| Indexed QM31 sampler / `ProverRwSampler` | zero, P, P+1, all-ff | AGREE |
| Indexed low digits / R2 copy and OrdinarySource copy | zero, P, P+1, all-ff | AGREE, including final quotients 0,0,0,256 |
| Indexed add-small | all P−1 plus 1; all zero plus 1 | AGREE, including carry true/false |
| CM31/QM31 byte writer | limbs 1,2,3,4 into 20 bytes of ff | AGREE; final four bytes retained |
| Statement points | ten base-field values 2 | AGREE; successor and absorption updates read |
| Fixed array copy; SHA zero/suffix padding | 1,2,3,4; ff buffer with nonzero marker/suffix | AGREE |
| SHA fallback block | state all 1, block all 2 | AGREE, all eight state words |
| Context encoder | two distinct 32-byte fields, fingerprints 4/5 | AGREE, all 81 bytes; actual version constant supplied |
| Batch1 indexed powers | base-field 2, N=3 | AGREE, all 24 output limbs |
| Tuple and forest producers | row550/start3/count3/tweak=true | AGREE, including final offset and remaining Zero limbs |
| Public-bytes / weights-new prototypes | nonzero fields; base-field alpha2 and circle coordinates3/4 | AGREE with exact native prototypes; not a proof of their original shipped associations |
| Owned encoder/mask cells | source value2 × factor3; zero cell replaced by one | AGREE with native owned helpers |
| Full prover closed helpers | active rows1/3/7, mask bits, dependent row7, level [1,2,3], query append2 | AGREE; whole native dictionary/effect claims remain SUSPENDED |

Additional successful isolated Full-body tests cover Boolean points, interpolation
accumulation/cell/extend/basis, assignment-bit writes, and M31/QM31 balancing.
Actual field primitive definitions and literal native constants were supplied
explicitly; no arbitrary complete ExternalFuns instance was invented.
`more-test-binding.json` pins the unchanged copied bodies and supplied leaves.
All **41 compared fresh projections agree**. The three divergent raw-kit
comparisons reuse the pinned emitted measurements and use a fresh native baseline.

The fresh native samplers produce P → `([0,1,0,0,0,0,0,0],0)`, P+1 →
`([1,1,0,0,0,0,0,0],0)` and ff →
`([255,2048,7168,14336,17920,14336,7168,2048],256)`. The inherited raw results
are respectively `([0×8],P)`, `([1×8],P+1)` and `([255×8],4294967295)`.
This confirms the existing translation-fidelity finding, not a shipped Rust bug.

Native harnesses compile exact copied bodies (and, where required, exact field
modules) with optimized rustc under capped sequential scopes. Structural record
and constant bindings are documented in `native*-source-binding.json`. Prototype
checks are explicitly labelled. No comparison is asserted against a rebuilt
release ELF. [test-import-pins.json](test-import-pins.json) records selected
objects and shared-source hashes; checked shared emission sources match the
repository candidates. Missing objects were handled by isolated exact small
body copies, not by overwriting shared sources or rebuilding the package.

## Row dispositions and central-ledger changes

[ROWS.md](ROWS.md) / [rows.json](rows.json) give 55 explicit row dispositions.
CREDIT STANDS preserves the previous local source/model scope; it does not close
an endpoint/native effect row. SUSPENDED preserves the theorem while withholding
its unchecked native attribution. Reference-only prototypes do not become
source laws through a successful finite test.

Required central-ledger wording change: **V388 must exclude the withdrawn raw
low-digit body and explicitly suspend the four raw bodies above**. Keep
V256/V257 OPEN without raw-emission credit. Retain the suspended
source-identification/body/native-composition rows V152–V154, V161–V163,
V165–V168 and zeroization/effect rows V221/V222 as P obligations. No currently
closed Stream B callback row is newly withdrawn by a divergence in its own
selected emission. V187/V201/V231/V232/V243/V259/V260 retain their existing
unproved generic/native-association obligations despite useful reference tests.
The central ledger was intentionally not edited by this evidence-only task.

## Validation, limitations and next deliverable

**Stopped on budget exhaustion: 40/40 charged Lean attempts (22 pass, 18 fail),
three uncharged reservation refusals, 0 Kani.** Eight native scopes ran (seven
pass, one pre-compilation path failure). Peak Lean RSS was 4,312,776 KiB; all
recorded swap counts were zero. No memory kill, timeout or cap increase occurred.
`receipts.json`/`receipts.csv` index every charged host run with target, exact
command, source revision/SHA, exit, wall time, peak RSS, swap and axiom-query
status. No theorem is added; test-only runs have `#print axioms = N/A`, while
retained generated-definition audits print only the standard accepted axioms.
Failed elaborations and admission refusals remain in the evidence. No evaluation
was forced past an unresolved declaration. No full manifest, SBF rebuild or Kani
run was performed. No unchanged full regression was repeated.

The test launcher and environment are private to the assigned host directory.
The initial J lookup failure was repaired only by import priority in that private
environment. Later missing objects were isolated to small exact testing bodies.
The first private fingerprints were per-test labels; the retained source hashes
show every retry changed its source or environment, and subsequent tests record
real environment/import-object fingerprints. Shared sources were never changed.
Reservation refusals used fresh IDs; admission always required both allowed:true
and exit0. The final timing audit found that 28122→28123 waited only
158.305 seconds, 21.695 seconds short of the required three minutes. This was a
procedural error; it is recorded rather than presented as a compliant wait.
The reservation scanner did admit 28123, and the unchanged memory/swap/task
caps remained in force. No further scope was launched to compensate for this. Native-003 failed before compilation on a
nested upload path; native-004 corrects that path and preserves the failed run.

The final six Vec-test modules were rejected because their shared testing
preamble omitted the R1Z qualifier on three field operations. The queue should
have been gated on its first result. All six failed outputs, including partial
independent #eval output, are rejected. The generator is corrected for the next
job, but was not re-run after exhaustion; the failed input files are preserved
byte-for-byte. Node-count isolation also remains suspended at the opaque
Option/Try carrier (`ExternalTypes`), rather than supplying an invented ABI.

This is a conservative audit and suspension packet, not proof that every
historical candidate or abstract native dictionary is faithful. The untested
mutation queue and ambiguous source associations remain visible and suspended.
Next deliverable: recheck the corrected six Vec test modules individually, then
pin the actual executable native dictionary/cohort for the
remaining Builder*/ProverRwFull mutation-bearing functions, then check each
remaining function and close its source association before using it in a real
RunJoin. The raw P3 body needs an owner-approved fidelity repair/re-extraction;
the four raw suspended bodies need their own unchanged executable checks.

Before/after endpoint and deployment premises: removed0, added0, weakened0.
T remains exactly entropy_law, entropy_kernel, observation. Application/proof
sources, release pins, keys and wallet/account authority are untouched. No push.

Final compile-free checks: all 22 successful test-source SHA256 values match the
delivered input files, all compared fresh projections agree. The exact reservation wait exceptions
are recorded in reservation-retries.json. `cleanup.json` hashes
and records removal of 23 rebuildable private artifacts (22 test objects and
one test binary); sources, receipts and every shared object/source were retained.
