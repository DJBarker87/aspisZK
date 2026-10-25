# Native query driver and total owned reference, 2026-10-25

Target not yet established: S1/S6 and both deployed 100-bit targets remain open.
S2 belongs to the transferred owner. No frozen production source changed.
Authoritative source is 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387;
see root design/RELEASE-LEDGER-20261025.md and the existing freeze reconciliation.

## Claim actually established

`S1OwnedQueryPairsFixedModelV1`,
`AspisS1OwnedQueryPairs.Model.reference_total_fixed`, proves TOTAL agreement
of the exact extracted owned eight-pair reference with fixed Q22 `scanOut`.
The domain is every typed pair of arrays of eight 32-byte blocks, with any
mathematical fallback state. The initial full 22-word buffer is zero, the
counters are zero, and all intermediate valid ranges are derived.
The result retains the complete final scanner state, selected bytes, and the
full native three-variant QuerySampleError datatype. On rejection it proves
the exact reached DrawLimitExhausted count and maximum 64. No sorting or
accepted-only projection is introduced. Final counters satisfy len <= 22 and
draws <= 64. No independent scanner law, successful scan, successful driver,
default-state law, or query canonicality premise appears in this theorem.

Before: the eight-pair reference-to-model bridge was missing; child scanner
and source-driver correspondence could not be obtained from the existing
accepted-only semantic model theorem. After: the concrete owned child and
owned driver are instantiated, with totality, default state, selection,
finisher, and all fixed-model transitions proved together. This is a source
reference theorem, not a whole SDK/caller theorem.

## Native source checks and their explicit cuts

1. `tools/s1-query-membership-current-20261025/check.py`: all 23 prefix lengths
0..22, symbolic complete array/candidate and draws <= 64, no cuts. The exact
native slice membership operation equals the extracted owned membership
helper. The same harness checks the full frozen word-body splice. 7,981
assertions passed, total 34.673984496s, maximum RSS 121,292 KiB, swap zero.
2. `tools/s1-query-block-cut-20261025/check.py`: frozen native QueryScan::scan,
actual native word decoder, full carrier and update/stop behavior, relative
to the exact owned block. Two pure membership cuts return a common arbitrary
reply tape. Universal observer coordinates check every reached membership
prefix/candidate and all output cells; reply selection does not depend on
those coordinates. 868 assertions, 25.218443225s, RSS 341,668 KiB, swap zero.
3. `tools/s1-query-pairs-cut-20261025/check.py`: original native
queries_from_pairs, QueryScan::default and finish execute unchanged. Two
full-state scan cuts return the same arbitrary bounded poststate/stop tape.
Universal call/word/byte coordinates compare full prestates, call inputs,
call counts and complete native results. 673 assertions; all accepted,
rejected and eight-call covers reached. 12.607221160s, RSS 716,920 KiB, swap
zero. Only unused dev-dependency metadata is removed from the fixture Cargo
manifest; actual library source/features are retained, with --features r0.

These are relative source checks. Their composition uses deterministic pure
membership equality and full-state block equality, plus pointwise trace
extensionality. They do not independently install an SDK/caller law. Kani's
native malloc-success/no-uninitialized-memory-check model is retained; this
is not an SBF/runtime or initialization proof. No opaque carrier replaces the
actual native state, errors, or original driver.

## Extraction, proof validation and pins

`tools/s1-query-pairs-reference-extract-20261025/check.py` checks 151 source
extraction pins, exact reference bodies shared with the native check,
normalization, focused Lean receipts, direct import hashes and warm R4 reuse.
The sole external computational leaf of the emitted driver is bound directly
to the existing checked `AspisS1OwnedQueryBlock.owned_block`; its raw external
axiom template is not imported. Emitted resource overrides are removed.
Only the NEW error type uses the existing checked
ImportUnionNamedDiscriminant naming adapter: the reader generator is the
same, only the generated instance name becomes type-qualified to avoid the
historical root-name collision. No other worker's sources/caches are edited.

Charon and Aeneas both exited zero for the unrolled owned reference, in
2 GiB capped NUC scopes, MemoryHigh 1536 MiB and MemorySwapMax=0. Previous
whole-loop Aeneas Not_found failures and rejected/codegen attempts remain
in source-only packets. The unrolling affects the isolated reference only;
the native original driver is checked unchanged against it.

Lean targets, compiled individually with the atomic local lock and
`lake env lean -j1 -M4400`, are the Types/Funs, StepModel, RunModel, Drive,
FinishModel, IndexModel and FixedModel modules named S1OwnedQueryPairs*V1.
Final bridge receipt: s1-owned-query-pairs-fixed-model-v1, exit 0,
21.062513042s, peak RSS 3,788,914,688 bytes, swap zero; #print axioms is
[propext, Classical.choice, Quot.sound]. The checker audits all other final
receipts and exact source/tool/direct-import pins. Failed proof attempts are
retained and are not accepted evidence. No unchanged full replay ran.

The old checked R4Transport2ScanComposition is reused with source SHA256
5c5850ed20123cbe96a59c08d61d5b9681ffd15df963f1ae3a48b8229fc533dc and
object SHA256 fe1af6d0ec3f9708e4c7aed48515fde6e5809964cd4662487311a74b514e91cc,
matching its existing successful producer receipt. Compiled binaries are not
part of this packet.

## Remaining enclosing premises and next deliverable

No enclosing SDK premise is claimed removed by this packet alone. The
existing first-only caller theorems still require concrete Stage1Extraction,
SDK/account/std/copy/allocator/runtime admission and the S1 installed backend.
The prior eta closure retains terminal-value canonicality. Native preparation
still has explicit arithmetic/Dotpush/finish cuts and scripted hash replies.
The full preparation/challenge trace, source-to-reference composition and
actual original caller instantiation must be joined without changing their
quantifiers, errors, effects, observer None or two-transaction semantics.
Release artifact/coherent replay pins remain necessary. There is no source
adoption decision in this packet: production code was not changed. Any later
candidate adoption requires explicit equivalence and re-pin gates.

Next: consume the total driver theorem and audited native boundaries in the
S1 preparation source/caller connection, eliminating the concrete query
helper premise rather than wrapping it in a new structure. Coordinate the
shared stage1 boundary with its S2 owner; do not duplicate that work.
