# Owned query scanner totality and exact membership, 25 October 2026

S1 and S6 remain OPEN; S2 remains transferred. The 100-bit target is not yet
established. No enclosing SDK/source/caller obligation is discharged by this
packet. No production source, source adoption or release artifact changed.

The authoritative release ledger is at repository-root
`design/RELEASE-LEDGER-20261025.md` (observed on research `8032aa56eb`), not under
this research design directory. The native reference pins the current
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` source. Existing freeze reconciliation
in `S126-FREEZE-RECONCILIATION-20261025.md` is reused unchanged. The complete
current core package and selected native source are retained in compile-only
source snapshots; no production file is modified by a checker.

## Exact claims established

The split owned Rust reference is in
`tools/s1-query-block-equivalence-20261025/proofs.rs`. Its membership, single
word and block operations use owned complete `[u32;22]` buffers and the real
usize counters. Charon and Aeneas extract these actual functions, with no
replacement field, callback, SDK/account or opaque scanner operation.

`S1OwnedQueryContainsTotalV1` proves TOTAL membership on every raw buffer,
candidate and prefix length <=22. `S1OwnedQueryStepTotalV1.step_total` proves
TOTAL word transition and preservation of len<=22/draws<=64, including both
stop guards. `S1OwnedQueryBlockTotalV1.block_total` composes those operations
with the extracted actual eight-iteration loop. It proves that every typed
32-byte block and bounded state returns normally and preserves both bounds.
The stop detection remains before each word, including no final extra check.
There is no canonicality, distinctness or successful-child-call premise.
These are TOTAL **on the stated bounded-state domain**, not unrestricted
arbitrary usize inputs or whole frozen SDK execution.

`S1OwnedQueryContainsMeaningV1.contains_meaning` proves that the same extracted
membership result is true exactly when the candidate occurs in the specified
prefix, by induction on the remaining prefix length. The follow-on
`S1OwnedQueryContainsStdV1.contains_eq_mem` gives full Result equality with the
membership predicate; `contains_eq_std` identifies that same result with the
already checked concrete Std slice-membership operation on the same prefix.
The latter retains a literal slice-content equality for its supplied slice;
it does not assume the desired membership or a second successful execution.

All source declarations are in `lean-candidates/s126-caller-boundary-20261021/`.
The generated functions are unchanged except removal of emitted resource
option overrides, retargeting the empty Types import and adding axiom audits.
`lean-binding.json` checks exactly those transformations. Default Lean resource
options, -j1 -M4400 and the atomic local lock were used. No custom axioms,
native decision procedure or admitted proof is present in accepted sources.

## Validation and failures retained

`tools/s1-query-block-equivalence-20261025/check.py` audits 61 extraction packet
pins, every accepted Lean source/receipt and the exact generated body changes.
Evidence is under `evidence/s126-current-caller-20261021/`:
`s1-query-block-extraction-v1`, `s1-owned-query-*`, and the named native attempt
histories. Only text/source/JSON/logs are retained; no LLBC, binary or object is
exported. Lean receipts contain exact source/tool/import pins, target, exit,
wall/RSS/swap and complete #print axioms. All accepted audits use only
propext/Classical.choice/Quot.sound, or no axioms. Maximum accepted Lean RSS is
2,276,524,032 bytes; zero swaps. No package replay was run.

The initial nested-loop reference failed Aeneas because Option was absent.
Adding the real Option language-item root exposed a pinned translator
Not_found error during nested-loop joining. Splitting membership, word and
block functions removed that obstruction: final Charon/Aeneas exits0, with
2GiB cap/high1536MiB/MemorySwapMax0 and no pressure. Both earlier failures are
retained and excluded. Initial local proof elaboration failures and their
compiler error-recovery sorryAx reports are excluded; final accepted sources
have standard-only audits.

The full frozen queries_from_pairs versus indexed reference check timed out
at500s, exit1, wall501.371192629s, RSS11,877,388KiB, swap0. The initial native
one-block comparison also failed; its exact terminal record is retained.
The split-reference block check failed with CBMC status6 at412.067471607s,
RSS10,813,412KiB, swap0, no pressure/OOM. A focused one-word diagnostic reproduced
status6 and revealed `map::at` while converting SSA to Z3 SMT2, before solver
execution. This is not a counterexample, and none of these native checks is
credited as correspondence. Existing R4 per-prefix/source-step certificates
remain available; the next composition must reuse them rather than replay
whole scans. A bounded one-word CaDiCaL diagnostic is separately recorded.

## Exact remaining obligations

1. Connect the frozen native scanner/array iterator and word decoder to this
   extracted owned reference, reusing existing checked R4 word/membership
   contracts and Lean induction. The failed whole comparisons do not supply
   this binding. Prove the complete selected-state driver, including all
   rejections and the following-block stop behavior, under that same binding.
2. Compose the resulting query operation with the already proved same-caller
   preparation/challenge trace and sampler value laws, retaining actual
   gamma scratch reuse, hash read order, errors and state effects. No new
   arbitrary scan/caller law may replace the missing concrete instance.
3. S6's existing decoded-public, first/first_decoded and owned-stage1 proofs
   retain the exact Stage1Extraction premise in S6SdkFirstOnlyV1. Its concrete
   native/SDK instance belongs to the transferred S2/shared boundary work.
   Library/sdk/std/copy/allocator/runtime admission and S1 backend installation
   remain explicit; second-stage/digest laws are already removed where unused.
4. Coherent enclosing source/caller replay and release re-pin remain required.
   These owned proof references are isolated candidates, not an adopted Rust
   replacement. Adoption would require complete source equivalence and all
   affected source/tool/import/artifact/CU gates; no adoption is needed merely
   to retain these reference proofs.

## Accepted native word partition and Std operation join

The symbolic-prefix one-word CaDiCaL check timed out at120s (wall120.897402743s,
RSS3,274,428KiB, swap0; high-pressure events23702, no max/OOM event). It is
excluded. The successful replacement fixes each initial prefix length0..22
separately, retaining arbitrary raw candidate/buffer words and draws<=64.
All23 native cases pass:7,958 assertions, total verification-command wall
27.569865319s, maximum RSS77,452KiB, zero swaps/pressure/OOM. Each case gets fresh
host admission and its own High3GiB/Max4GiB/Swap0 scope, one job at a time.
At prefix22 only the stopped branch is reachable:1/2 covers is expected;
all other cases satisfy both covers. No assertion or range check is disabled.

`tools/s1-query-step-equivalence-20261025/check.py` verifies370 retained native
packet hashes, all23 terminal receipts, complete current QueryScan source plus
its proof-only appended helper, exact frozen word-body splice (only receiver
self->scan), and byte-identical owned membership/step bodies in the successful
Aeneas extraction. This is a complete single-word helper Result/value check,
not execution of the original complete QueryScan.scan loop. All22 post-buffer
cells, both counters, stop and range bounds are checked. No result stub is used.
The old larger failures remain separate. The qualifier in each attempt's exact
source/harness/command takes precedence over inherited compile-only block
labels; metadata-correction.json records this without rewriting old receipts.

`S1OwnedQueryWordStdV1.owned_step_eq_stdWord` proves FULL Result equality of the
same owned word step to the complete retained concrete Std word operation,
including actual prefix read, contains, array update and checked additions.
Prefix success and membership meaning are derived on len<=22; draws is not
restricted for this equality. `stdWord_total` then derives totality/ranges when
draws<=64, with no independent child success. Final focused check exit0,
12.874258750s/RSS2,257,207,296B/swap0, standard-only audits. The new word
interpretation retains the full buffer/counters; it does not install the native
array iterator or replace the enclosing SDK computation.

No enclosing SDK/caller premise was removed by these new helpers. The exact
remaining native iteration/word decoder/driver composition in item1 above is
still owed. The existing enclosing S1/S6 first-only and eta premise removals
remain as recorded in S126-FIRST-ONLY-CALLER-20261025.md and
S1-FINAL-ETA-20261025.md; they are not newly claimed by this packet.

Whitespace validation: maintained tools/Lean/design pass git diff --check.
The raw evidence logs and frozen generated top_overflow.rs snapshots retain
upstream trailing whitespace verbatim to preserve their recorded hashes;
the unrestricted evidence-inclusive whitespace check reports those existing
bytes. No retained evidence or frozen source was reformatted.
