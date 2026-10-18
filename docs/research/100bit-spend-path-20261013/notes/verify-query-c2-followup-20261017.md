# Follow-up to lead deb68369b

Integration branch: `codex/r1-lead-followup-20261016`, isolated worktree
`/Users/dominic/ZK/.worktrees/r1-lead-followup-20261016`.
Baseline: `deb68369ba3ad7cc6706dc24b6503fac1cbe942b`, which accepts
`0189f1094`. The candidate production source is the Digest32 version at
`a555c852664c80000942f0c911e16719a5493625`; its two changed production files
are source-identical in this integration branch. The live worktree and modules
were left alone. No SBF build or readonly runtime harness ran.

## Authorized source changes and extractor blockers

Decisions1d and1e were applied exactly: move the verifier tail into
`verify_finish`, and unroll the eight query digest pairs. The independent
forward/reverse patch audit restores the lead source exactly.

Standing Decision1f then covered these changes, in order:

1. The query trace enumeration fixed point blocked extraction. Expand the
   fixed22 trace statements in the same order; preserve the decoder-returned
   state, errors and trace values.
2. The semantic-round loop fixed point blocked extraction. Expand its ten
   iterations in row order15–24.
3. Borrow translation required moving the unchanged row14 initializer and
   ten-round sequence into private owned-argument helpers. The cfg-specific
   tuple returns carry the same running value, alpha, transcript and prover
   round-check vector.
4. Move the complete unchanged `let boundary = ...` and `let value = ...`
   statements into private helpers. No arithmetic rewrite was made. Their
   implementations remain explicit boundaries in the reachability model.
5. Whole-phase generated printing saturated indentation. Move the unchanged
   single iteration into a private owned helper and call it ten times. The
   first cfg-on-assignment spelling failed Rust parsing and is retained as a
   rejected attempt; the final cfg-exclusive helpers use direct tuple
   assignments. Both helper bodies reverse exactly to the predecessor.

Every source step, blocker and patch is retained under
`tools/callers-current-extraction-kit/standing1f-*`. The independent audit is
`evidence/verify-query-followup-integration-20261017/exact-refactor-reverse-audit.json`.
It checks both cfg alternatives, exact moved statement bytes, all fixed loop
positions, state carry, and the unchanged lead files. No new inline/cold
attributes, public signatures, hash/sampler operations or arithmetic changes
were introduced.

## Native gates on the final source

All targets exited0 with process swap0 and cgroup swap0 under
MemoryHigh=6GiB, MemoryMax=8GiB, MemorySwapMax=0. Native #print axioms is N/A.
Full commands, revisions, source manifests, admission reservations and raw logs
are retained in the linked evidence directories.

| Target | Result | Wall seconds | Peak RSS KiB |
|---|---|---:|---:|
| codec1233-final | all1233 outputs byte-identical | 68.480971 | 540900 |
| saved-proof-counter-final | ordered583 calls identical,349/234 | 114.957637 | 541300 |
| checkpoint23-final | same23 tests pass | 45.790352 | 472296 |
| verify-real-s2-default |112 comparison cases,55 fault points, both observers|4.767929|248192|
| verify-real-s2-detail |112 comparison cases,55 fault points, both observers|3.796710|246860|
| query-migration-102 |102 comparison cases,16 digest positions and decoder|5.044606|261744|

Clean gates: `evidence/final-a555-clean-native-20261017` (archive
`c4acd85d649d75630260a1915ef43c9ec524dcb240bcb2ced45ae5180ab20c0e`).
Injection gates: `evidence/verify-query-native-20261017` (archive
`5c192d1d15fea5207c1f8bb386708b68654ae121dca00eef85792731c2821427`).
Both independent read/hash checkers pass without executing builds.

Verify faults cover Prefix parse, public_transcript, begin, the moved row14
initializer and every lookup/decode/boundary/semantic failure in rows15–24.
The saved S2 proof uses real production arithmetic and transcript operations.
Query tests use saved S2 and synthetic S1/two-fold contexts; the latter are
not asserted to be valid proofs. Digest32 failures use caught aborts because
the trait is infallible. Errors, returned values, state, trace marks and
observer phases are compared in full. The query run at5a28 is re-pinned by
byte equality of transcript.rs and530 other production files; only
r1_semantic.rs changed afterwards. Superseded5a28 verify runs remain historical.

## Current compiled proof results

`evidence/semantic-rounds-current-20261017` retains81 exact source cuts, valid
LLBC, the generated definitions and the bound compact model. The focused
model target exited0 in2.572s at2660300KiB RSS; the ordered-ten-row theorem
exited0 in5.462s at2700816KiB RSS. Both had swap0; all six #print axioms
reports contain standard axioms only. Actual helper success supplies rows15–24,
the exact returned alpha order, unchanged hash, and transcript state carry.
It does not assume arithmetic success or individual child-call success.
Decoder/fold implementations are explicit ordinary function boundaries.

Actual full verify_finish emission is also retained and valid. Emission alone
is not counted as a compiled theorem. The bound model and caller composition
are now checked in `evidence/finish-actual25-a555-20261017`: three targets,
19 standard-only axioms reports,14 exact body bindings, five fixed actual-round
identities, and seven canonical helper identities. The initially compiled model
was rejected by its axioms audit because root `try_into().unwrap()` inherited
`core.fmt.Formatter`. The final model exposes that exact typed callee as an
additional universal interpretation API; the failed model and log are retained.
No root-conversion implementation theorem is claimed. The final model has eight
explicit arithmetic/allocation/circle/root-conversion APIs, plus the existing
round decode/fold boundaries; source control flow and first-error branches remain.

`evidence/source-full25-frames-20261017` and
`evidence/verify-helper-prefix-fe80-20261017` retain the checked source-frame
construction and actual first→tx1→verification-prefix helper reachability.
`evidence/typedfull-current-20261017` adds25 coherent focused targets and69
standard-only reports. Its names-only RecordParser discriminant repair retains
the exact11 tags and inverse audit;23 exact reverse importers and two wrappers
are rebuilt, reusing69 source/object-pinned cached modules.

`ActualFull25.first_full25` now derives the full25 result from actual first
acceptance through fixed actual tx1/verify prefix/begin/finish. It constructs the
ordered source Call list, proves its frames equal the parsed completedRecords,
and supplies strict typed decoding and the901-byte bound. It assumes neither
hbytes nor child-call success. The focused target exited0 in3.018s, with four
standard-only reports and swap0; its full RSS/command/revision receipt is in the
three-target finish manifest. The selected hread/htyped/ha compositions are
checked below with their explicit conditions; see also
`notes/full25-hread-dependency-map-20261016.md`.

`evidence/opening-circle-current-20261017` adds four coherent focused targets
and16 standard-only axioms reports:

| Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| ExtractedOpeningCalls |0|2.512|2632668|0|
| ExtractedOpeningQueriesReachability |0|6.042|2760744|0|
| ExtractedCircleCalls |0|2.287|2646532|0|
| ExtractedOpeningRun |0|2.085|2646908|0|

All use sourcea555 and6/8GiB swap0 scopes; exact commands and import pins are
retained in the packet. These prove circle25/26 record bytes, all three digest
calls per circle row and state carry; the actual row26-state constructor digest
for opening reseed; actual query absorb plus the decoder-returned state; and the
literal six-row27–32 two-fold or five-row27–31 S1 opening schedule with final
prepared-state/hash carry. Child-call success is derived from actual model
success, not added as a premise. The failed circle proof input is preserved.
`evidence/actual-allrows-sampler-current-20261017` now checks the outer
composition and current sampler transport: nine targets,43 standard-or-empty
axioms reports, all exit0/swap0 under6/8GiB caps. The all-rows target takes
2.511s at3893540KiB RSS; transport takes2.290s at3865016KiB RSS. Exact
commands, revisions and every prerequisite receipt are in its SUMMARY and archive.

`ActualAllRows.first_all_rows` derives the same semantic/prepared objects,
ordered semantic25 run, actual circle calls and bytes, row26 reseed, actual
opening state chain and final prepared state from one outer first-control-flow
success. Its literal schedule is range33 for two-fold or range32 for S1. It
assumes no child success, source run or byte equality. The listed arithmetic,
decoder and embedding interpretations remain explicit. The concrete SDK metadata
projection remains the single separate R16ReadonlyMetadataProjection premise;
literal custody and syscall-effect interpretation are not inferred from it.

The sampler refresh retains current objects for eight same-source cache
conflicts and rebuilds only seven missing reverse dependents plus the transport.
Current QM31 equality and the existing decodeState/blockRank are reused. The
coordinate order remains c0.a,c0.b,c1.a,c1.b. A missing cached server sidecar
failed before elaboration; its input/receipt is preserved, and exactly pinned
sidecars repaired the environment without a proof change or repeating green checks.

`evidence/selected-read-current-20261018` restores the focused current
selected-read dependency closure:215 project targets,1540 standard-or-empty
axioms reports and17 explicitly compile-only prerequisites. All exit0 with
swap0; maximum process RSS is3747384KiB. Exact per-target wall times, commands,
revisions and producing identities are retained in archive
`845b29aff9117e9f4cb7ca515343968802c24bcb5c74e6a9fa8bf72ee63fa048`.
The root read/hash checker passes. Two proof-only import splits preserve the
qualified Public and sigma/rhoOf/semantic_row declarations byte-for-byte.
A failed square-root normalization is replaced by a symbolic rational bound
with the same theorem statement; three axioms-print formatting repairs change
only scoped pp.fullNames. Every rejected attempt is retained. This packet
restores generic selected-read lemmas; the actual source-record and typed
trace compositions have their own focused evidence below.

`evidence/source-read-current-20261018` adds the source-record instantiation:
`ExtractedSourceSemanticSampler` exits0 in2.768s at4088716KiB RSS, and
`ExtractedSelectedSourceRecords` exits0 in2.748s at4139704KiB RSS. Each has
five standard-only axioms reports and swap0. Archive
`0cb3b8609059747e6cd026a32f95fe610d4d0975dee99bf6914089cd01bb0398`
retains exact commands/revision, three rejected local sampler proofs and the
coherent6110-module input snapshot; the root read/hash checker passes.
The sampler equality uses actual Call.sample, current QM31 equality and the
existing semChal definition, with no extra q-equality premise. The record
theorem constructs bounded selected records from actual first success and
derives the completed-read hread premise from the same strict parser. It uses
emptyTable plus an explicit oracle and recoverC2 callback. Equality of those
completed challenges to the source q-list, already-read typed recovery and
literal word custody are not claimed by these two leaves.

`evidence/source-trace-prerequisites-20261018` checks six minimal generic
typed-recovery prerequisites and `ExtractedSourceDigestOracle`: seven targets,
26 standard-only reports, all exit0/swap0. The oracle target takes3.217s at
3874916KiB RSS; full per-target metrics and exact revision/source/import pins
are retained in archive
`7dbd428c81ee45c8aa631e75b075cbed7cac472c6fc559709cae65a556e3de65`.
Its read/hash checker passes. The typed core preserves the original qualified
definition, statement/body and namespace/open/section context; the original
Table-context failure is retained and excluded. The source oracle derives
functional correspondence from actual successful Digest32 calls by proving
exact input grouping from flattened bytes. DigestAt and SHA distribution are
not premises of this leaf. Its grammar covers the fixed initializer and
semantic/circle calls; the four-slice opening grammar and unrelated runtime
hash calls remain outside it. The length-association reject is retained.
Actual typed-table recovery is checked in the later caller packet below;
literal custody remains separate.

`evidence/source-read-actual-first-20261018` supplies the actual caller read
with the exact returned challenges, through three focused targets:

| Target | Exit | Wall seconds | Peak RSS KiB | Swap | Standard reports |
|---|---:|---:|---:|---:|---:|
| ExtractedSelectedSourceAgreement |0|2.979|4149744|0|5|
| ExtractedSourceTraceIndices |0|2.100|2647940|0|9|
| ExtractedSourceReadFromFirst |0|3.199|4145812|0|1|

Archive`bc700a9bb9e352f529ed4fd87123699a8fc4b7a56cc789384efba0646ef05409`
retains exact source/revision/commands/imports, failed focused attempts and
the current6124-module output snapshot. Its root read/hash audit passes.
`first_source_read` starts at the fixed actual first caller, derives the same
initializer serializer vector/length and public bound, constructs H from D,
and proves hread and semChalsZ with exactly the returned challenges plus alpha
under the fixed sourceChallenge map. Table consistency with that constructed
H is explicit. No hbytes, child success, chosen H, extra sampler success or
q-equality premise is supplied. The actual tableBefore typed/ha composition
is checked in the next packet below; literal C1/C2 word custody remains open.

`evidence/source-typed-actual-first-20261018` completes the same-witness
typed-table composition with five focused targets:

| Target | Exit | Wall seconds | Peak RSS KiB | Swap | Standard reports |
|---|---:|---:|---:|---:|---:|
| ExtractedSourceTypedRecords |0|4.168|4141124|0|7|
| ExtractedSourceTypedRecovery |0|2.368|4152752|0|4|
| ExtractedSourceObservations |0|2.590|3852172|0|15|
| ExtractedSourceCanonicalRecovery |0|2.369|4149240|0|2|
| ExtractedSourceFirstTyped |0|2.798|4161224|0|4|

Archive`d8b49fb97a8c6b3398f69693822305dbeac3991908721c89fc84faa539efc9ed`
retains exact commands, production revisiona555, proof-source hashes, all
rejected and superseded attempts, and the coherent6130-module snapshot. The
root read/hash checker passes all five targets and32 standard-only reports.
No predecessor is newly counted or replayed. The checks use6/8GiB swap0 scopes
and the shared host Lean lock; no Lean jobs remain active.

`SourceFirstTyped.first_typed` derives the actual initializer, same25 source
records and strict bytes, exact returned challenges and same t25 circle25
absorb from one actual first/finish witness. It constructs77 relevant source
observations, proves consistency and target membership (`ha`), and derives
`htyped` at that same tableBefore under the explicit existing badColl no-hit
condition. Exact source-q hread/semChalsZ uses that SAME table and record list.
No child-success, hbytes, chosen state/target or htyped premise is supplied.
The source segment is not asserted to equal the whole native583-call log.
Lifting all three facts to a larger trace explicitly requires observation
inclusion, consistency with the same H, a first-read budget and no-hit. Raw
typed recovery supplies the actual C1 root bytes and framed records; literal
C1/C2 words and typed-context/publicBase/extraClaims custody remain separate.

`evidence/source-address-current-20261018` adds two focused source-address
leaves: `ExtractedSourceDigestAddresses` exits0 in4.085s at3882588KiB RSS
with19 standard-only axioms reports; `ExtractedSourceCircleFrameBound` exits0
in2.795s at3854120KiB with one standard-only report. Both have swap0 and
the same6/8GiB caps. Actual public_transcript success supplies its serializer
bytes, constructor and successful length conversion. The same actual row
Call supplies the three ordered digest inputs and state carry. The next
circle row25 has3712 payload bytes and3717 frame bytes; this is separate from
the901-byte bound on the first25 semantic rows0–24. This two-leaf packet exposes
`DigestAt` as a finite functional interpretation premise. The later source
oracle/caller packets above discharge it for their grammar, while literal
context and word custody remain separate. The packet retains four rejected proof
iterations and two external-lead prelaunch suppressions. All subsequent Lean
jobs share the lead's `/tmp/aspis-r0-lean.lock` and retain the external-job guard.

## C2 proof frontier

The earlier nine owned-host and four recorded-experiment model results are
**HISTORICAL_CONTEXT_ONLY**, excluded from the current release count. Their
import paths selected incompatible historical FS2/Uniform objects. The
classification audit retains three exact witness paths and selected source and
object hashes under `evidence/c2-historical-context-20261017`; original archives
were not overwritten.

`evidence/c2-host-embedding-20261017` supplies a fresh four-target proof cone
over current Aeneas/backend imports only. Eight primitive lemmas prove the
actual canonicalized QM31 embedding and retained c0 projection. Six generic
construction-core lemmas and two binding lemmas were freshly checked in that
same environment. All28 axioms reports are standard-only, all targets exit0
with swap0, and the3937-module source/object closure is hash-audited. The
actual embedding is canonicalized limb-by-limb modulo P; no raw-limb identity
is substituted for it.

These results do not yet prove actual Backend/build execution constructs the
owned vectors or literalMessage. Packing, variant/encoder transport and exact
length/content, salt/path, custody, and checkpoint remain separate obligations.
Hashes and samplers are not substitutes for the full C2 witness.

The remaining compiler frontier is isolated in
`evidence/c2-helper-root-diagnostics-20261017` (archive
`9b64fe50df2f41656258a777ce5144a91a2c8858755587f6cc82fbc3b63b93b0`).
Rooting the actual copy helper alone still fails Aeneas at
`SymbolicToPureAbs.ml:1313`; rooting only the unchanged encode/retain prefix
fails at `InterpAbs.ml:191`. Both have valid error-free LLBC but no accepted
Lean emission or theorem. Their Charons exit0 and their Aeneas runs exit2,
with swap0 and the same6/8GiB caps. The retained102-member archive and
deterministic input generators pass the read/hash-only checker. No viable
production-source refactor was demonstrated or adopted. The six exact source
spans and preservation conditions are recorded in
`evidence/c2-host-embedding-20261017/next-source-bridge-plan.json`.

The read-only `evidence/c2-recorded-current-audit-20261018` finds295 additional
candidate modules,109 current-base boundaries and unsupported
`AspisV8R19.R572SequentialWordMass` for the unchanged four recorded-experiment
theorems. This list has not been run. Its review-only proposal pins49 exact
declarations across12 possible definition cores while preserving the actual
protocol witness/relation/extractor and transcript recovery/replay. The
SpendRelation/Merkle definition closure is not yet a small executable plan.
No historical object is reinstated and no formal result is claimed by this
read-only audit.
The preliminary generated-declaration parser included trailing proof commands
in eight of49 model definition segments. All49 original body-hash labels are
superseded; their original proposal is retained. The corrected model command
parser checks qualified names, command/signature hashes and ordered context.
Its read-only checker passes; graph counts and the no-run conclusion are
unchanged, and no formal result depended on the preliminary proposal hashes.
The final source-only definition-use supplement pins19 spend commands across
six interfaces and62 Merkle/typed commands across16 interfaces. Its broader
43-interface accounting retains the actual sampler, replay/compiler and exact
relation/decoder/default semantics; it is neither an absolute Lean-file lower
bound nor a closed executable refresh. Generated/private/instance bindings and
the actual UnifiedSampler.samp dependency remain the precise frontier. The
supplement hash is56aafd576984f052d0fba71ba8d689bc506753107ad6b55baeebfa56e95197f7;
the root read/hash checker passes with zero compiler jobs or formal results.

## Outstanding work

Actual finish→full25 byte identity, current selected-read closure, fixed
source-derived oracle/challenge agreement, and same-source-table hread/ha
and conditional htyped are checked. Remaining obligations are actual embedding
in the full experiment/runtime trace, its stated consistency/budget/no-hit,
and literal C1/C2 word/context custody. Actual Backend/build owned-witness
execution remains blocked by the recorded Aeneas failures; the recorded-cut
compiler's small current definition closure is not yet demonstrated.
Packing, salt/path, custody and checkpoint remain separate C2 obligations.
Circle25/26, row26 reseed,
query returned-state carry, opening schedule and the outer all33 composition
are checked. Declaration re-pinning is complete for the explicitly registered
accepted/current universe:341 unchanged,90 re-extracted, one authorized
projection replacement, zero unresolved. Its exact source revision,70.341393s
wall,612483072-byte RSS, swap0, retained hashes/diffs and rejected predecessor
inventory are in `evidence/verify-query-followup-integration-20261017`.
