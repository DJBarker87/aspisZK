# Lead note on the R1 soundness gap map (2026-10-19)

Accepted: `R1-SOUNDNESS-GAP-MAP-20261019.md` (worker branch
codex/r1-soundness-gapmap-20261019, eight commits, read-only). Spot checks:
`checked_acceptance_failure_bound_no_model` is at
`lean/RawChecksAdaptiveFailureNoModel.lean:34` with the hypotheses `hQ`,
`htag`, `hchecks`, `hN` as listed; `tx2_authenticated`, `resume` and
`finish_relation` exist in `crates/aspis-r1-cost-probe/src/verifier.rs`
(lines 450, 379, 332) and have no mention in `lean/` or `lean-candidates/`.

## Reading

Of 52 links to the target theorem (T): 14 proved, 1 proved-stale, 10 re-pins
owed (the ten kept CU candidates and the whole-cone inventory), 4 refinements
owed, 15 open, 8 premises. The Lean model of the protocol is essentially
complete (M1–M9); the gap is the source side. The largest single open item is
stage 2: `tx2_authenticated`, `resume`, the 12-query loop and
`finish_relation` have no extraction and no owner. The closest composed
theorem bounds model-acceptance-without-extraction by 12Q²/2^256 +
N·15/2^109 + 2^-126 for a free decoder, decision and prover; nothing ties it
to the deployed transactions yet.

## Decisions

1. **Step 0 (freeze the verifier source) is now tied to the proof-size
   test** (`PREREG-PROOF-SIZE-20261019.md`). If the candidate format is
   viable, the freeze is taken on the new format, not the current one, so
   the re-pins (S1–S10), the stage-2 extraction (R14), Merkle acceptance
   (R13) and the commitment words (R12) are done once. The commitment-layer
   items the format change touches are open today, so changing the format
   first repeats no proved work. If the format is not viable, step 0 is
   taken on the current source and the critical path runs as written.
2. The three source candidates on the R3 row (heap overwrite helper,
   accumulator zero-initialisation, composition array copy) are not adopted
   until step 0; their adoption is a user decision at that point.
3. The ROM, Aeneas-correctness and toolchain premises are to be re-accepted
   in an R1 note (they are dated 2026-08-25 for V5 in
   `docs/assumptions-ledger.md`); to be written at step 9.
4. `verifier.rs`'s admission hash in `FINAL-SOURCE-ADMISSION.json` is stale
   by the prover-only error variants (`.text` identical, LEAD-REVIEW-
   CU-BOUND-2); re-pin at step 1.
5. Statement binding is proved for withdrawals only; transfer joins at step
   8.

Unverified by the worker, carried as open: host receipts for
`ConcreteBinding`, `LiteralClassifier`, `SpendRelation`,
`LiteralAcceptanceTerminal` (status rests on the lead reviews); the extracted
sources behind the proved source rows were not diffed against current
production Rust; the root checkout's uncommitted `current-merkle-source-
execution` evidence is not counted.

## Addendum (2026-10-19, late): integer-overflow semantics as a gap-map row

Aeneas translates Rust integer operations with checked semantics: an overflow
is a failure of the translated function. Rust release builds wrap unless
`overflow-checks = true`. The two extracted prover-side crates
(`aspis-r1-cert-check`, `aspis-r1-cert-build`) have overflow checks on in
release (root `Cargo.toml`, D73), so the compiled checker is the modelled
function. The SBF programs (`programs/r1-cost-probe`, `programs/aspis-pool`)
have no overflow setting and are built wrapping.

For (T) the needed direction is "deployed accepts ⇒ model accepts". If the
deployed verifier wraps at any operation where the model fails, that
direction is not established. New row **R22 (OPEN)**, owner lead/Codex:
one of (a) a Lean proof that no operation in the stage-1 and stage-2
extraction cones can overflow for any input (per-operation range lemmas;
the builder work already has "u64 reductions mod p never overflow",
LOG:6076); (b) an SBF build with `overflow-checks = true` for the verifier
program, re-measured against the stage-1 CU margin (16k); or (c) an audit
that every arithmetic site on the admitted routes uses explicit
`wrapping_*`/`checked_*` operations (23 in `fast_pairing.rs`, 10 in the
adapter today), with the model matching by construction. R22 is on the
critical path before step 9 (C3). Size: M for (a), S for (b) and (c).

Prover side: measure how much of the 35.8 s P_R1 check is the overflow
checks before deciding between a no-overflow proof and keeping them on.

## Addendum (2026-10-20): M10 composed, conditional

Codex job cx-m10 (commits d1281b25f, f7c7392a8) landed.
`RawExtractorCostComposedV2.recorded_extractor_cost_and_failure`
(`lean/RawExtractorCostComposedV2.lean:124`) bounds the accepted-run expected
field, hash-log and bit cost of the recorded-run extractor by an explicit
polynomial and carries the exact M9 failure bound with δE = 2^-126 ≤ 2^-120.
Four targets compiled locally (exit 0, ≤ 2.23 GiB, standard axioms;
receipts in `evidence/extractor-cost-composed-20261019/`). Status of row
M10: PROVED (conditional). Named implementation hypotheses still to
discharge: output refinement, bounded arithmetic jobs, implementation
overhead, log-read accounting, bit accounting, uniform overhead
constants/degree. These join the source-side list (step 9 inputs).

## Addendum (2026-10-20): R22 partial

Codex job r1-overflow-free (a85e60cd0 after WIP 93f5025d9, 9d906cec2) landed:
`design/OVERFLOW-FREEDOM-INVENTORY-20261019.md` and
`evidence/overflow-freedom-20261019/` (36 focused targets, 50 theorem reports,
standard axioms, ≤ 3.00 GiB). Proved: decoder value/loop totality, ρ
push/value totality, control and index bounds, the field/semantic-loop/
parser/folded-dot range proofs. No admitted-input overflow was found.
R22 stays OPEN: the pinned stage-1 extractions predate the CU optimisations
(weights, private pairing, fast dots have no extracted bodies yet), so their
overflow proofs wait for the S1–S9 re-pins; then round/prepare composition,
the outer decoder guards, the global ρ caller invariants and the
deployed-to-checked bridge. Sequence: S1–S9 → R22 (stage 1) → R22 (stage 2,
after R14).

## Addendum (2026-10-20): binary commitment model landed

Codex job r1-commit-model (5e3d9b2c4 after 61e1a7928, d217103e1): 25 `Bin*`
modules (`design/BIN-COMMITMENT-MODEL-20261019.md` maps each to the
eight-way theorem it replaces), 106 theorems, standard axioms, ≤ 3.03 GiB,
receipts in `evidence/bin-commitment-model-20261019/`. Proved at the model
level for the binary format: node/leaf grammar, multiproof ⇒ per-query path
acceptance with dedup preservation and padding isolation, opening binding
with collision targets counted as 6·Q²/256³² (the κ input), causal word
recovery and compiled-run word stability. Rows M7, M8 and R11's model half
are PROVED for the binary format; their eight-way versions stay as history.
Obstruction (same as D77.2): unconditional disjointness of node preimages
from arbitrary public-byte hashes is false (`verifier.rs:382` hashes public
bytes verbatim); separation is proved under a length premise, to be
discharged from the fixed public-statement length in R-wire. Source side
(R12, R13, R14) continues in the stage-2 extraction.

## Addendum (2026-10-20): R8 proved; R9 stated

Codex job cx-bindings (690327fe0): the transfer-variant statement binding is
proved over the pinned adapter extraction (metadata, asset, checkpoint and
lane bindings, exact transfer payload, recipient/change commitments,
payment-encoder success); two new modules, standard axioms, ≤ 3.27 GiB
(`evidence/transfer-bindings-20261020/`, `design/TRANSFER-BINDINGS-20261020.md`).
Row R8: PROVED. Row R9 (same statement across stages) is now stated
precisely as named obligations with the conditional byte-equality and
supplied-public parsing proofs done; transaction reachability and the
checkpoint linkage (R15) remain open and wait on the stage-2 extraction.

## Addendum (2026-10-20): R17 model half proved

Codex job cx-geometry (360512b5b): seven modules, 31 theorems, standard
axioms, ≤ 3.76 GiB (`design/FOLD-GEOMETRY-20261020.md`,
`evidence/fold-geometry-20261020/`): fold algebra, the optimised inverse
formulas, child indices, quartet rotations, fourth powers, the stored
x18/x16 geometry, natural-basis commutation and the D18 bitwise permutation
equality; all 1,024 fast-domain constants validated independently. Row R17:
model half PROVED with explicit table-content premises; the source-execution
half (the full `QueryGeometry` iterator/grouping path and runtime
arithmetic, candidate 7) closes with the S7 re-pin and the stage-2
extraction.

## Addendum (2026-10-20): R4/R18 partial

Codex job cx-sampler (4b5b3a6b2, 86fe4174f): four modules, 20 theorem
audits, standard axioms, ≤ 3.27 GiB (`design/SAMPLER-ROWS-25-32-20261020.md`,
`evidence/sampler-rows-25-32-20261020/`). Proved: source block/state
correspondence for the circle rows (25–26) and the opening scalar rows
(27–30), the row-26 reseed, the nonzero-γ handling, the model query law
(row 31), and the tag and commitment-message formats conditional on the
public mapping and `Checks`. Still open on R4/R18: scalar/circle output
transport, the source query-scan refinement (row 31 source side), the
current CU re-pins (candidate 7), the global-log/full-prefix composition
(R10), and the deployed public mapping; counterexamples record why
unrestricted variants and free public tags cannot satisfy the laws.

## Addendum (2026-10-20): R10 partial; R15 finding

Codex job cx-ckpt-log (163ee546b): four modules, 12 audits, standard axioms,
≤ 3.20 GiB (`design/CHECKPOINT-LOG-TX1-20261020.md`,
`evidence/checkpoint-log-tx1-20261020/`). R10: the tx1 log assembly is
proved conditionally, rows 0–24 composed with the sampler-suffix results
through shared-oracle bridges; complete tx1 call coverage stays a named
premise; the tx2 half and cross-transaction consistency wait on R14.
**R15 finding:** the accepted stage-1 extraction exposes `finish`
(`tx1_finish`, which writes the checkpoint) as an unconstrained function
parameter — the checkpoint writer and the account write were never
extracted; countermodel theorems show the boundary admits arbitrary output
bytes. Ruling: `tx1_finish` and the checkpoint writer are extracted with the
same pipeline as stage 2, pinned once at the combined freeze (after the
stage-2 borrow fix lands), as job "cx-tx1-finish"; R15 then has both halves.

## Addendum (2026-10-20): R-wire tx1 inventory; three more record classes

Codex job cx-wire-tx1 (120424d31): inventory of all 31 syntactic tx1 digest
sites with construction, length, tag and dependency
(`design/WIRE-TX1-20261020.md`); three modules, 15 audits, standard axioms,
≤ 3.31 GiB: parser-to-duplex framing, all 45 digest calls in `begin`, and
the opening constructor/block facts under explicit width premises.
Finding: the "typed records only" target as stated was false — tx1 also
hashes the 57,607-byte compact proof, the 1,880-byte ASF8 account and a
1,758-byte checkpoint checksum input. None of these lengths is 31 or 65, so
the D79 separation extends to them; the record-class list in D79 and the Bin
model is to be extended by these three (job cx-record-classes). Full
deployed correspondence and the privacy premises eCm/ROpen/RComLog remain
open on the caller, optimised-source (re-pin), compact-expansion and
log-transport dependencies named in the report.

## Addendum (2026-10-20): R19 stage-1 constant

Codex job cx-qv-stage1 (26c7d8c49): `stage1Budget k = 43·k + 165`, hence
595 distinct first reads at ten queries (115 transcript + 30 leaves + 447
parents + 3 checkpoint hashes), proved conditionally for the binary format
with the FS2 distinct-first-read bound and the binary cost embedding; three
modules, 16 audits, standard axioms, ≤ 3.24 GiB
(`design/QV-STAGE1-20261020.md`). Both measured stage-1 variants match the
count. The old 328-call constant in `VerifierCallBudget` is for the retired
eight-way format and cannot certify a 595-call trace; the new constant
replaces it in the hQ instantiation. R19 stays open on: compact-source
coverage via the re-pins, the privacy read-set transport, the stop-label
refinement, the opaque `B.finish` (the R15 finding), and stage 2.

## Addendum (2026-10-20): R14 extracted

Codex job cx-stage2b continuation (14 commits through 41b2dd71b): the
stage-2 cone translates with the pinned Charon/Aeneas after isolating the
`&v` loan (the relation View is reconstructed after the queries) and the
later loan scopes; 55 attempts receipted
(`evidence/stage2-continuation-20261020/REPORT.md`). All 21 gates pass on
the final source; six-fixture CU meets PREREG-2 item 1 with minimum margins
281 CU (stage 1) and 201 CU (settlement); verifier ELF 9672cc48…
(1,506,920 bytes), measured WITHOUT the deployment-id data slots, which
landed on research separately. Proved locally on the extraction: fixed
parse-length equality, checkpoint proof-digest equality under comparison
soundness, twelve ordered query calls with the increment. Row R14:
EXTRACTED (source pinned; refinement open). Next: one combined gate run and
ELF pin on the research tip (ids + stage-2 refactor) = the freeze; then
cx-tx1-finish (R15), the final CU bound, devnet.

## Addendum (2026-10-20): R15 extraction blocked on the frozen source; refactor prepared, not applied

Codex job cx-tx1-finish (c5183dc19): Charon extracts the checkpoint
serializer, pinned Aeneas fails with "Could not match the contexts" at
`verifier.rs:330` (`for root in &p.roots`); verifier source unchanged, 58
frozen pins match (`design/TX1-FINISH-20261020.md`). Ruling: the freeze
(`LEAD-FREEZE-20261020.md`) stands. The minimal source change that lets the
tx1 finish cone translate is prepared and gated on a side branch
(cx-tx1-finish-prep) and NOT merged; it is folded into the next freeze
together with any other source change the R14 refinement requires, so the
re-pins and the CU bound are reopened once, not per finding. R15 stays open
until then; the devnet deployment and the final CU bound proceed on the
current freeze.

## Addendum (2026-10-20): R15 preparation; the account write is an audit item

Codex job cx-tx1-finish-prep (branch codex/cx-tx1-finish-prep-20261020,
commits 6a7d2d816, 24c99396d; RETAINED UNMERGED for the next freeze): with
the checkpoint serialisation loops isolated, the checkpoint writer and the
compact finish cone extract with the pinned Charon/Aeneas; all standing
gates pass on the refactored source (P_R1 8/8; six-fixture CU with minimum
margins 119 CU stage 1 / 134 CU settlement; candidate ELF 4aa7e8a1…).
Proved locally: writer length, conditional determinism, writer/resume
digest agreement (standard axioms). Blocker: the adapter's account write
indexes `AccountInfo` slices, whose type carries mutable borrows; pinned
Aeneas rejects it and the slice-pattern alternative alike. Ruling: the
account-write fact of R15 ("stage 1 writes only into an all-zero,
verifier-owned account of exactly checkpoint_size", G_R1.7/G_R1.9) is
discharged by an audited source map of the adapter write path (the V5
accepted-source-map pattern) beside the runtime premise P2, not by
extraction; the extracted writer facts cover everything up to the write.
R15's remaining proof items: unconditional digest preservation and the
guarded account-write audit. The refactor is folded into the next freeze.

## Addendum (2026-10-20): R16 partial, with the field audit

Codex job cx-hchecks (772de5b07): `hchecks_partial : Nonempty (Checks pub rs)`
under explicit remaining hypotheses, deriving the opening and semantic
parses, query decoding and residual batching from the proved source facts;
a conditional public-parser composition; five audits, standard axioms,
≤ 3.41 GiB. `design/HCHECKS-20261020.md` tables all 26 fields of `Checks`
with the supplying fact, the exact gap and the owner. Finding: no deployed
protocol-decoder/decision instance is yet justified by the available
refinement, and a counterexample shows a free decision cannot establish
R16 — the decoder/decision instance must come from the stage-1 + stage-2
extractions (R14 refinement, R-wire). Remaining field groups: transcript,
checkpoint (R15), reader, pairing, accumulator and the semantic endpoints.
R16 stays OPEN; this table is the working list for closing it.

## Addendum (2026-10-20): R10 stage 2 and cross-transaction consistency

Codex job cx-log-tx2 (1d973fd4d): the three resume digest witnesses and the
conditional tx2 log assembly are proved; tx1/tx2 shared-oracle log
consistency is proved through a common byte interface; the checkpoint
digest linkage is stated with explicit frozen-writer/provenance premises
(the parked tx1_finish writer agreement is cited as a named premise until
the next freeze); five modules, 17 audits, standard axioms
(`design/LOG-TX2-20261020.md`). A direct combined import of the stage-1 and
stage-2 generated modules fails on a generated instance-name collision
(evidence retained) — the combination goes through the byte interface for
now; the collision is an extraction-hygiene item for the next freeze. R10
stays conditional on: complete call coverage (R-wire tx1/tx2), backend
correspondence, writer preservation/provenance (R15), ordering and
first-read accounting (R19).

## Addendum (2026-10-20): R-wire stage 2

Codex job cx-wire-tx2 (da030f9cd): every stage-2 digest site inventoried,
no record class beyond the D79 list; eight modules (resume inputs, binary
parents, slice widths, conditional leaf-backend correspondence), 24 audits,
standard axioms, ≤ 2.27 GiB (`design/WIRE-TX2-20261020.md`). The
unrestricted API-level target is false (an empty public slice can reach the
public rehash through the raw API); the caller-scoped statement replaces it,
which matches the deployed entry (the adapter supplies the fixed-length
public bytes, D79). Open: whole-tx2 log composition, the concrete
leaf/conversion boundaries, and the full eCm/ROpen/RComLog discharge.

## Addendum (2026-10-20): R22 stage 2 partial

Codex job cx-overflow-s2 (4bb0fca91): inventory of the stage-2 cone's
failing integer operations (`design/OVERFLOW-FREEDOM-S2-20261020.md`); six
modules, 39 theorems, standard axioms: layout constants, checked
arithmetic/control bounds, opening access, two array accessors, an
unwrap-parametric reader. No admitted-input overflow found. The concrete
reader proof exposed the `core.fmt.Formatter` axiom (the Aeneas opaque type
already ruled non-release in D71.4); that receipt is rejected and the
reader is kept parametric. Three direct-helper counterexamples show the
cursor, geometry and residue-phase invariants are necessary; their
reachability from tx2 is the composition still owed. R22 stage 2: partial,
pending the concrete backends and loop invariants (R14 refinement).

## Addendum (2026-10-20): R13 partial on the binary format

Codex job cx-r13-refine (cd24eea6f): seven modules, 16 audits, standard
axioms, ≤ 2.26 GiB (`design/R13-REFINE-20261020.md`). Proved on the
stage-2 extraction: exact source leaf bytes/tags/salts under the named
WIRE-TX2 laws, the binary byte-carrier transport, the exhausted terminal
conditions, equality of the source read set with the Bin model's, and the
dedup/padding composition to per-query executable path acceptance. R13
stays OPEN on: the accepted-source-run implication (sorted-key/dedup and
mutable-array simulation, source padding-scan correctness, whole-run read
coverage, caller composition), and batch A (stage 1) on the S7 re-pin.

## Addendum (2026-10-20): R12 conditional on the binary format

Codex job cx-r12-words (7701a4dcb): five modules, 20 audits, standard
axioms, ≤ 3.48 GiB (`design/R12-WORDS-20261020.md`). Proved conditionally:
C1 (row 0) and folded (row 30) whole-word stability, accepted logged
opening projections, the actual source-frame targets, the row-0/row-30
literal constructors, and a stage-2 folded-leaf adapter. Row R12: PROVED
(conditional), mirroring R11, on the Bin recovery modules. Remaining: the
R10 composition and accounting, R13's source acceptance/decoding/read
containment, the folded payload/checkpoint linkage, backend/conversion
correspondence, caller re-pins and scalar transport.

## Addendum (2026-10-20): the deployed decoder/decision instance

Codex job cx-decoder-inst (57d1c639f): `hchecks_deployed_partial` over the
exact compiled run with explicit source obligations, the public
serializer/binding composition, a conditional universal `htag`, and the
conditional hQ shape QP + 595 + Q2 (two modules, six audits, standard
axioms; `design/DECODER-INSTANCE-20261020.md`). The instance itself cannot
yet be fixed: the frozen stage-1 extraction leaves `B.finish` opaque (the
R15 finding) and the stage-2 first facts do not yet give the
authenticated-source-to-compiled-rows map (the R14 finish refinement, in
flight). A checked counterexample shows two different protocol decoders can
produce identical verifier behaviour, so the decoder must be fixed by
construction from the extractions, never inferred from acceptance.
Consequence: R16 closes only after the next freeze (tx1_finish extracted)
and the R14 finish refinement; both are already queued.

## Addendum (2026-10-20): R19 stage-2 constant

Codex job cx-qv-stage2 (021b68804): `stage2Budget k = 43·k + 50`, 566 at
twelve queries; verifier-core allowance 595 + 566 = 1,161 distinct first
reads; conditional batch-B cap of 563 commitment positions; three ordered
resume digest witnesses; `finish_relation` makes no designated digest call.
All twelve measured stage-2 rows show 545–563 SHA calls, under 566. Four
modules, 19 audits, standard axioms, ≤ 2.23 GiB
(`design/QV-STAGE2-20261020.md`). R19 is now stated for both transactions
on the binary format; it stays conditional on complete source-prefix
coverage (R-wire), the trie/privacy transport, backend/runtime
correspondence and any separately designated external reads. The hQ
verifier half for the deployed instance is 1,161.

## Addendum (2026-10-20): R14 finish refinement, conditional

Codex job cx-r14-finish (5d268e741): the extracted `finish_relation`
supplies the `pairingChecks`, `firstMatch` and `residualBatch` fields of
`Checks`, composed with the parser/digest facts and the twelve ordered
queries; stored-domain fold bridges, the candidate-12 reducer transport and
the finalized-weights handoff are proved; twelve targets, 26 audits,
standard axioms, ≤ 3.43 GiB (`design/R14-FINISH-20261020.md`). Row R14:
refinement PARTIAL (conditional). Remaining: the named backend/re-pin
premises (S8, S9, S4/S5), the R13 acceptance items, accumulator
finalisation, and R15 provenance. With this, every `Checks` field has
either a supplying theorem or a named missing lemma (see
DECODER-INSTANCE-20261020.md); the composition into R16 waits on the next
freeze and the re-pins.

## Addendum (2026-10-20): R15 adapter write audit

Codex job cx-adapter-audit (82e3e6292): `design/R15-ADAPTER-WRITE-AUDIT-20261020.md`
maps every account write on the admitted routes: stage 1 [3,10] makes one
checkpoint copy after the ownership, distinctness, exact 1,768-byte size,
all-zero and verification guards; stage 2 writes no account (return data
only); lifecycle routes 4/5/6 are rejected by the release entrypoint. Three
new host tests (37/37 passing) cover occupied/wrong-size rejection,
unauthorised upload/sealing and release rejection of lifecycle attempts.
**Close-authority finding:** there is no checkpoint-close instruction at
all; tag 6 seals a legacy buffer and needs the recorded authority's
signature. No arbitrary-close griefing path exists. Two product notes,
outside (T): a blank checkpoint account has no creator reservation, and
checkpoint rent (1,768 bytes) has no refund route — a wallet/lifecycle item
to decide before release. With this audit beside P2, R15's account-write
fact is discharged by source map; the writer facts remain on the parked
freeze candidate.

## Addendum (2026-10-20): query-scan exhaustion bounded; R4 row 31 source boundary

Codex job cx-queryscan (d09bc1482): five modules, 29 audits, standard
axioms, ≤ 2.87 GiB (`design/QUERYSCAN-20261020.md`). Proved on the model:
the query-scan exhaustion probability (fewer than 22 distinct indices within
64 draws of 8 words from 2^18 positions) is ≤ 2^-454 (exact value ≈
2^-559.8), so the prover's `Error::Transcript` abort (D74.4) enters both
error budgets as a negligible abort term; the report gives the exact
insertion points (soundness: an abort term beside the bank-abort 2^-126;
privacy: an abort premise beside D73.4/D74.4). Also proved: stable first-22
ordering, distinctness, block/word agreement, generic abort accounting.
R4 row 31's source closure stays open: the pinned abstract `B.decode` admits
duplicate indices and arbitrary continuation states (checked countermodels),
so the concrete driver/library correspondence and source-to-ROM coupling are
required — the same R-wire items as elsewhere.

## Addendum (2026-10-20): S7 blocked on the frozen source; refactor goes to the candidate freeze

Codex job cx-repin-s7 (5a2c1f4f1): Charon succeeds on the candidate-7 cone,
pinned Aeneas exits 2 at `verifier.rs:257–264` (the `Option<&mut
BatchedWeights>` reborrow loop in `accumulate_with_node`); no Lean emitted;
source unchanged (`design/REPIN-s7-20261020.md`). Inventory finding:
`query_with_geometry` is audit-only now; the production owners are
`candidate::query_values` and `accumulate_batched_with_node` — the S10
inventory must be reconciled to the production owners (session A). Ruling:
the minimal reborrow-loop refactor is stacked on the parked candidate
freeze (branch codex/cx-freeze-prep-20261020), gated there, and S7 with its
R22/R17/R13 joins re-pins against the candidate; S7 is therefore a
next-freeze item, like R15.

## Addendum (2026-10-20): S6 re-pinned on the verifier side; adapter half is an audit item

Codex job cx-repin-s6 (127878968): `first` and `first_decoded` extracted
from the frozen source with the pinned Charon/Aeneas; `first_success`
re-proved on the new bodies (row R6 is no longer stale), full-result
equivalence and decoded-statement reuse proved through the documented
boundary; local range/index lemmas (the R22 cone part); 11 audits, standard
axioms (`design/REPIN-s6-20261020.md`). Blocker: the adapter's `accounts[0]`
read at `r1_pool_adapter.rs:950` is `SliceIndexShared<AccountInfo>`, which
pinned Aeneas cannot translate — the same tool boundary as R15's account
write. Ruling: S6's adapter half (the stage-1 caller binding: which account
bytes feed `first`/`first_decoded`, same-byte binding to the checkpoint) is
discharged by extending the R15 adapter source-map audit to the stage-1
account READS (job cx-adapter-audit2), beside premise P2. Row S6: PROVED on
the verifier cone; adapter binding by audit.

## Addendum (2026-10-20): S2 re-pinned on the verifier side

Codex job cx-repin-s2 (3d16b68c8): `observer`, `first_decoded` and `first`
extracted from the frozen source; caller success re-proved with the
observer off (the shipped configuration) and symbolic equivalence at the
retained boundary; standard axioms, 3.25 GiB (`design/REPIN-s2-20261020.md`).
The adapter-side translation stops at the same `AccountInfo` indexing as
S6 (`r1_pool_adapter.rs:950`); covered by the adapter read audit
(cx-adapter-audit2) beside P2. Row S2: PROVED on the verifier cone.

## Addendum (2026-10-20): S8 blocked on the frozen source (fourth translation blocker)

Codex job cx-repin-s8 (77b3b6815): Charon succeeds; pinned Aeneas fails in
`compact::check_values`' borrowed `chunks_exact` loop; one concrete
residue-update iteration is proved total (`S8FrozenRow.row_step_total`,
standard axioms); source unchanged (`design/REPIN-s8-20261020.md`). S8 stays
REPIN-OWED. Ruling: this is the fourth translation blocker on the frozen
source (checkpoint writer, roots loop, `Option<&mut>` reborrow loop,
`chunks_exact` loop). Rather than stacking them one at a time, the next
candidate-freeze pass (cx-freeze-prep3, after prep2 lands) extracts EVERY
admitted-route cone — stage 1 including tx1_finish, stage 2, the
candidate-7 and candidate-12 cones including `compact::check_values` — and
fixes all remaining blockers in one gated pass, so the adopted freeze is
fully translatable and no re-pin can stop on a borrow pattern again.

## Addendum (2026-10-20): adapter read audit; the adapter premise is now one sentence

Codex job cx-adapter-audit2 (eada5714e): `design/R15-ADAPTER-READ-AUDIT-20261020.md`
maps the stage-1 and all seven stage-2 account reads with their guards and
the exact slices handed to the extracted entries; stage 2 reconstructs the
public bytes and has no public-buffer account. Two new host tests pass
(proof/public mutation rejected at resume and authenticated tx2; wrong
lengths and every duplicate-key pair rejected at stage 1 without a write).
With the write audit, the whole adapter boundary that Aeneas cannot
translate reduces to premise P2 plus one sentence: "the runtime presents the
same account bytes to both transactions when the checkpoint digest
matches." That sentence is to be stated as P2′ in the R1 premise
re-acceptance (design/R1-PREMISES-REACCEPTANCE-20261020.md, step 9).

## Addendum (2026-10-20): R13 closure pass

Codex job cx-r13-close (7bf72ae88): eleven modules, 22 audits, standard
axioms, ≤ 2.25 GiB (`design/R13-CLOSE-20261020.md`). Proved: the source
sort preserves the occupied-prefix key support; each dedup step preserves
exactly the prior pairs plus the current one; the complete binary inner
level loop equals a functional fold of its buffer writes; padding chunk
coverage, prefix slicing and tail divisibility. Still open on R13: the
whole dedup-scan transport, the eighteen-level parent/sibling simulation,
the zero-scan backend semantics (the generated `Iterator.any.default`
interface is missing from the extraction and a countermodel shows the
abstract interface is insufficient — an extraction-hygiene item for the
candidate freeze pass), whole-run read coverage, and the accepted-tx2
composition; batch A on S7 (candidate freeze).
