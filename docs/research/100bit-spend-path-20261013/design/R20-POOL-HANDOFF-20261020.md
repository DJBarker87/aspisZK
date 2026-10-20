# R20 Pool handoff: proved parts and remaining premise (2026-10-20)

Branch `codex/cx-r20-pool-20261020`, source base
`6bb2b9cb1f2517b51763ed09b16b8716d3226caa`. The adopted verifier remains
`b2727acd3`; neither it nor the parked candidate nor any production Pool
source is changed. The [byte/account audit](R20-POOL-HANDOFF-AUDIT-20261020.md)
is the AccountInfo handoff evidence under P2, following the R15 audit ruling.
Paths in this note are relative to `docs/research/100bit-spend-path-20261013/`.

## Exact scope of the formal result

`lean/R20PoolHintStrip.lean` proves total execution of the **actual pinned
extracted** `split_pair_forest_terminal_bump_hints_v1` for every bounded byte
slice with length at least four: its body is the prefix of length `len-4`,
and the original slice is precisely that body followed by the four returned
hints in their declared order. This is not a proof that arbitrary hint values
pass PDA/custody authentication. Source: `programs/aspis-pool/src/pair_forest.rs:139`.
The new generated `lean/AspisR20Pool/{Types,Funs}.lean` are byte-identical to
pinned Aeneas output. No existing module was edited.

`lean/R20PoolStatementAgreement.lean:40` proves equality of the Pool field-copy
map and retained adapter common record under `sameSnapshot` (:34). The
transfer (:46) and withdrawal (:58) theorems then prove identical output for
**any same deterministic encoder** on the complete reconstructed statements.
They use actual successful retained reconstruction, preserve the full variant
and public record, and require the audited snapshot agreement. This is a
conditional congruence theorem, not an extracted Pool caller or actual ASQ8
encoder round-trip theorem. The Pool map is explicitly defined at :16 against
`pair_forest.rs:1473–1502`; tying that map to Rust execution remains audited.
The two full statements are not equal across variants.

The retained adapter reconstruction cone is unchanged: all five cut hashes
match `tools/adapter-reconstruct-extraction-kit/source-pins.json`, independently
recorded in `evidence/r20-pool-handoff-20261020/retained-adapter-pins.json`.
`ExtractedAdapterTransferBindings` and `ExtractedAdapterWithdrawalBindings`
retain the actual metadata validation, asset binding, checked increment and
nullifier-to-lane binding described in [TRANSFER-BINDINGS](TRANSFER-BINDINGS-20261020.md).
The structural name `AuthenticatedAsq8Accounts` does not prove owner/PDA facts.

## Explicit extraction stop

The pinned Charon succeeds for the actual ASQ8 request encoder with
`has_errors=false`; pinned Aeneas exits **2**, with `Failure "Unreachable"`
at `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:442–448`,
`interp/InterpAbs.ml:1955` (the payment-variant match / borrow abstraction join).
No replacement model, code refactor, candidate adoption, tool patch or cap
increase was attempted. Exact ASQ8 decode/re-encode byte identity therefore
remains source-audited and host-tested, rather than an extracted Lean theorem.
The stopped item is not advertised as proved by the generic encoder theorem.

Diagnostics retained: the initial encoder start root was scoped to a dependency
rather than the owning crate and yielded an empty output; it is rejected as
scope evidence, then corrected to the aspis-statement manifest. Initial strip
output left Option::ok_or opaque; explicitly including that exact Rust std
method produces the accepted extraction, without adding a library axiom.
The unused external template is represented by hash/size only. These are
changed-scope/configuration attempts, not unchanged regression reruns.

## Host tests and reproducibility

The initial optimized host suite passed **119/119** (0 ignored), including existing
successful transfer/withdrawal settlement controls and three added tests:

- `r20_hint_reorder_variant_and_stale_request_reject_before_cpi`: an unused
  transfer vault hint changed to 1, master/checkpoint order swapped, outer
  kind swapped while retaining ASCP, and an older sequence-0 request supplied against a canonical newer
  sequence-1 checkpoint all reject before any verifier/System/token CPI and leave every
  account's data and lamports unchanged.
- `r20_strip_reencode_is_exact_for_both_payment_variants`: actual Pool strip,
  exact ASQ8 decoder and encoder round-trip both transfer and withdrawal for
  256 varying four-byte suffixes; sub-four-byte inputs reject. This parser
  test intentionally accepts arbitrary suffix values; the first test and
  existing exhaustive bump tests exercise authorization.
- `r20_cpi_exact_bytes_and_order`: invokes the real dispatch planner/runtime
  shell with existing selected-registry fixture, asserts exact 320-byte encoder
  output and all seven meta keys in order, checks read-only/non-signer metas,
  and rejects the registry/entry permutation. The existing MockRuntime also
  checks every meta matches its AccountInfo and the executable is last.

No tracked Pool or verifier file was edited. Because the fixture and shell
are private, `tools/r20-pool-handoff-kit/` injects new test items into the final
`cfg(test)` modules of a **disposable host source copy**. The dispatcher test
is derived from the existing complete fixture with extra assertions. The
unmodified production copy matches all 487 manifest inputs; the test copy
has exactly two test-only file deltas with original/instrumented hashes.
This is not an SBF source change or a replacement runtime implementation.

Host `/home/dombarker/project-offloads/codex-cx-r20-pool-20261020/`;
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Cargo -j4,
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. Expected time was compilation then
unit tests, without elimination or proof generation. Rust wall 27.408 s,
peak RSS 556,632 KiB, process swaps 0; runtime 0.53 s. The revised stale-sequence case then passed the three focused tests in 6.475 s
(peak 422,568 KiB, zero swaps). Finally the exact frozen Pool feature set
passed **121/121** in the complete library suite once in 7.645 s (peak 424,216 KiB, zero
swaps), including the final stale-sequence case. This feature change exercises
the full ASF8 result-validation/source-invariant path; the initial feature set
used the optional direct-result consumer. No unchanged regression was repeated.
Initial 16-GiB bounded host reservation plus this job remained under 55 GiB;
resource snapshots are retained. The test target cache is a separate copy
of retained native artifacts; no existing cache/source/object is overwritten.

## Premise left for C3 and privacy

`R1FinalSoundness.BoundaryStatements.R20 : Prop` at
`lean/R1FinalSoundness.lean:53–54` and evidence field `h_R20 : s.R20` at
:111–112 are external proposition slots. These artifacts do not construct
a proof of arbitrary `s.R20`. For an operational instantiation, the remaining
premise is: **every accepted stage-1/Pool/nested-stage-2 pair uses the same
request, authenticated account storage and live snapshot at the mapped keys;
the nested instruction executes the selected frozen program on precisely the
mapped bytes; its returned candidate is the verified proof prefix; and its
reconstructed ASF8/semantic public is the public committed by stage 1.**

The source map and pure theorems narrow this to the runtime shell (P2:
owner/privilege/PDA provenance, immutable release selection, no intervening
mutation of the read-only snapshot, CPI account matching/demotion, return-data
provenance and transaction rollback), compiler/backend correspondence (P6),
the stopped exact request codec theorem, and the separately open R9/R15
checkpoint/proof/public-byte provenance across transactions. No hash-collision
exception is silently removed. Canonical stored bumps rely on the Pool-write
invariant, not merely one create_program_address call. Native metadata flags
are models of runtime enforcement, not evidence of validator enforcement.

A previously retained checkpoint can be valid indefinitely; a universal
“all non-latest statements reject” target is false. Counterexample by source:
`pair_forest.rs:2190–2192` deliberately permits the earlier retained checkpoint,
and :1357–1379 compares request against that supplied checkpoint rather than
a mutable latest sequence. The tests instead reject the old sequence against a newer supplied checkpoint; stale *live* public against stage 1 remains the digest binding question.
Likewise a claim that transfer and withdrawal full statements are identical
is false: ASQ8 byte 5 and payment magic/kind differ. No such theorem is asserted.

The privacy final definition of done still needs its source ScanCouplings,
complete ordered logs, query accounting and source experiment transport
(`r1p-final/PRIVACY-FINAL-20261020.md` in the separate privacy research tree).
This handoff audit and conditional deterministic equality do not supply those
couplings or turn C3 into unconditional deployed soundness.

## Verification receipts and diagnostics

Packet: `evidence/r20-pool-handoff-20261020/manifest.json`, schema
`focused-extractor-proof-packet-v1`. Each receipt records the exact target,
command, source SHA/revision, direct-import object hashes, exit, wall, peak RSS,
swaps and complete axiom lines. `object-pins.json` and `source-validation.json`
represent Lean/native/LLBC artifacts by hash and size only; no binaries,
objects, archives or LLBC are committed. All six audited production files,
including Pool, adapter and both codecs, match frozen b2727acd3 byte for byte.

| Focused Lean target / accepted attempt | Exit | Wall s | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| ExtractedAdapterWithdrawalBindings / withdrawal-prerequisite-v1 | 0 | 5.494 | 2265939968 | 0 |
| R20PoolStatementAgreement / statement-v2 | 0 | 2.067 | 2246475776 | 0 |
| AspisR20Pool.Types / strip-types-v1 | 0 | 2.224 | 2254372864 | 0 |
| AspisR20Pool.Funs / strip-funs-v1 | 0 | 12.798 | 2236252160 | 0 |
| R20PoolHintStrip / strip-proof-v5 | 0 | 4.171 | 2256830464 | 0 |

The five new theorems (including private list_four) audit to subsets of
`[propext, Classical.choice, Quot.sound]`; two additional reports audit the
unchanged withdrawal prerequisite. Generated module options are retained
unchanged; no handwritten overrides, new axioms or admitted proofs. Local
Lean 4.32.0 uses exactly -j1 -M4400 -DElab.async=false, the shared mkdir lock,
process gate, `/usr/bin/time -l`, and private
`/tmp/codex-cx-r20-pool-handoff-20261020-objects`. Existing caches are read
only. No package-wide, frozen-manifest, SBF or arithmetic release aggregation
was run. Extraction attempts were restricted to the two named cones.

Failed preflights found missing private prerequisite objects before starting
Lean. Inventory drafts queried two nonexistent backend theorem names; proof
drafts corrected the subtraction spec's conjunction, a let-pattern reduction
and explicit Rust Result constructor types. Their error-recovery sorryAx
lines remain historical diagnostics and are excluded from accepted evidence.
One failed attempt found the shared lock directory externally absent at
cleanup; its compiler receipt was preserved, and cleanup now tolerates an
already absent directory. No process was killed for memory or retried at a
higher cap, and no unchanged source/environment check was repeated.

The extra exact-feature Rust run was initially refused **before a scope or
compiler started**: 48 GiB of populated reservations plus 8 GiB would exceed
55 GiB (`resource-gate-rejection.json`). While packet assembly continued,
other jobs completed. A fresh read-only snapshot allowed the same capped
launch, which then passed. No other agent's job was killed or altered.

Check the whole packet without replaying a build:

```
python3 -B docs/research/100bit-spend-path-20261013/evidence/r20-pool-handoff-20261020/packet.py
```
