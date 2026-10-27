from pathlib import Path
p=Path('design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md')
s=p.read_text()
s=s.replace('<!-- CIa_WORDING -->', '''Each paragraph below is proposed text for recording an already authorized scope.
The D188 paragraph is chosen separately in the next section. None takes effect
through this draft. Exact kernel quantifiers in L8a_008 remain authoritative.

**S2TrustedSdkBorrow.** We trust the documented data-borrow semantics of the
pinned `solana-account-info` 2.3.0 and production lock, together with its Rust
RefCell/Ref/RefMut guard interpretation, exactly as the fifteen fields of
`AspisR1.S2Trust.S2TrustedSdkBorrow`. The relation associates actual typed account
cells, payloads and counters with valid abstract heaps and preserves reply and
next heap under the fields' enabledness, lifetime and counter guards; it includes
guard acquire, move, dereference and drop, error move/drop, framing and liveness.
Authority is C3-BIN 2026-10-23 01:20 (D177), LOG D189 2026-10-23 17:35, and the
fresh L8a_008 field prints. This trust supplies no caller success, output bytes,
log, child join or complete execution refinement. Ref clone/map_split/leak,
realloc, Rc clone/free, lamport borrows, CPI, reentrancy and concurrency are outside
this item.

**TrustedStd — slice copy, with W1.** We trust the pinned Rust standard-library
`slice::copy_from_slice` semantics for valid exclusive/shared borrowed references:
equal lengths copy the source contents into only the destination payload;
unequal lengths panic. The exact abstract hypothesis is
`AspisR1.S2W_TrustedStd.TrustedStd.slice_copy_from_slice`, whose specification
quantifies all abstract states and payloads. LOG D157 2026-10-22 08:35 and C3-BIN
2026-10-23 18:05 authorize the native valid-reference interpretation; L8a_008 and
TRUST-AUDIT W1 document the width mismatch. **W1 remains a qualification:** the
total abstract extension does not assert native semantics for invalid references;
every actual use must have justified validity/admission, or a restricted interface
must be proved. This paragraph neither discharges nor widens that association.

**TrustedStd — pure Option/Result.** We trust the pinned standard-library
interpretations of `Option::ok_or` and the selected 32-byte Result unwrap operation,
exactly `AspisR1.Port1_Library.TrustedStd.option_ok_or` and `result_unwrap32`,
including their specified failure cases. Evidence is LOG D157 2026-10-22 08:35,
C3-BIN 2026-10-23 18:05 and 2026-10-25 late trust separation, and TAu_030/L8a_008
prints. These pure value laws do not imply native frame, ownership, allocation,
unsafe-memory or whole-body effects correspondence, and do not import prover
collection, entropy or I/O trust into the soundness theorem.

**P1 ideal-oracle realization.** We retain the existing P1 boundary for the
selected fixed native digest and the model oracle, exactly
`AspisR1.S2W_ExtractionBoundary.P1.realization`:
`∀ bytes, sha256 bytes = H bytes`. This is an explicit ideal-oracle interpretation
condition at that supplied world, not a proof that native SHA-256 is random or
that one fixed function equals every sampled oracle. Evidence is C3-BIN
2026-10-23 11:05/18:05 and L8a_008's fresh definition. Query-restricted cylinder
coverage in the ARX candidate is a separate theorem and does not weaken or remove
this retained global field. This paragraph introduces no all-world native hash
identity and no new cryptographic assumption.

**P6/Kani association.** We trust the pinned Kani/CBMC tool route as evidence for
an explicitly checked association between the exact shipped unsafe/non-extracted
body and its owned safe reference, preserving Result at the required success
boundary, ordered effects and buffer contents on the certified domains. We then
use Aeneas extraction of that reference. Authority is C3-BIN 2026-10-23 02:40,
LOG D188 2026-10-23 16:40, C3-BIN 2026-10-25 late §4 and 2026-10-26 native Vec/Box
(b); the actual certificates and their pins must support each use. This accepts
the tool boundary, not an unchecked association or an enlarged domain. Unsafe
MaybeUninit/uninit/raw writes remain proof obligations. The returned mathematical
`MultiproofConeP6Frozen2Stage.P6Boundary` is not evidence that a whole deployed
batch was checked, and no new Lean P6 axiom is asserted.

**P7 compiler and pinned implementation base.** We trust the selected compiler,
LLVM/platform tools and ABI, and the release-pinned Lean/Mathlib/Aeneas library
base, for the exact source/features/toolchain and artifact selection recorded by
the release receipts, including the three H5 ELF pins listed below. Authority is
C3-BIN 2026-10-25 late §4, the 2026-10-26 replay-scope ruling, and LOG D188
2026-10-23 16:40; RPz8/L8a_HostPins identify the selected proof objects and the
S10 re-pin3 evidence identifies the binary pins. Library cache reuse is not a
fresh library replay. Tool trust does not itself prove a concrete source-to-ELF
association; source hashes alone do not prove semantic lowering. This item does
not approve arbitrary extern templates, nonstandard imported axioms, unsafe
source refinements or changed source/features/toolchains.

**Standard logical axioms.** The permitted logical base is exactly a subset of
`propext`, `Classical.choice`, and `Quot.sound` for each new top theorem and for
the audited roots. This follows the job's r1p-common §3 and local-lean §4 rules,
reaffirmed 2026-10-27; L8a_006 prints exactly those three for both fresh roots and
L8a_007 independently walks their kernel dependencies. This permission does not
accept the 105 unreachable nonstandard imported axiom declarations: they remain
UNRECORDED under the strict import-wide audit and need separate resolution or an
explicitly scoped audit decision. No such decision is made by this appendix.

**Historical checkpoint interfaces — no additional trust.** The seven indexed
`S2X.CheckpointVersionBinding` and
`S2W_AuthenticatedInputs.CheckpointVersionBinding.history` fields retain their
historical conditional meanings (physical key, ledger, events, saved/loaded
association and no intervening write), as recorded by C3-BIN 2026-10-23 11:05/18:05
and TRUST-AUDIT 2026-10-26. They are not independent free trust arguments of the
fresh tops. Today's required history must be derived from the approved game,
data-only RuntimePersistence and source proofs; their presence in an imported
or reachable interface neither authorizes assuming that deployment instance nor
adds a full-account persistence item. The 2026-10-26 owner amendment controls.

For the three **already named** runtime items, the exact scopes remain:
RuntimeEntrypointAdmission supplies only the initial valid typed/abstract relation,
fresh tracked guards, zero counters/external borrows, live accounts and key/cell
alias consistency for the two entries; RuntimeSyscall constrains successful
returning digests (`hashv parts = ok digest → decodeState digest = sha256 (flatten parts)`),
without totality/termination; Allocator supplies private-state `allocate/cleanup`
operations without a proposition guaranteeing success or account mutation rights.
C3-BIN 2026-10-23 02:40/11:05/18:05 and LOG D189 fix these scopes. RuntimePersistence
is exactly the owner-approved data-only `CPR_DataPersistence.TwoTransactionLaw`.
The older [runtime proposal](RUNTIME-PERSISTENCE-ITEM-20261026.md) contains
pre-adoption “no trust item adopted” text; the later binding owner amendment
supersedes that status, not its narrow law or its source-association caveats.''')
s=s.replace('<!-- CIa_D188 -->', '''These are alternative replacement paragraphs, not cumulative permissions.
The left preserves the current Result-level reading; the right is the requested
trace-level clarification/extension in [L166-DECISION](../docs/research/100bit-spend-path-20261013/design/L166-DECISION-20261027.md).
Owner approval of the inventory alone does **not** select the right column.

| Result fidelity — current reading | Trace fidelity — proposed reading, not adopted |
|---|---|
| **AeneasExtraction (D188).** We trust the pinned Charon/Aeneas translation as the source semantics of the particular extracted Rust bodies and their recorded source/producer pins. At the owned-adapter interface this is exactly `S2W_DigestExtraction.AeneasExtraction.stage1`, `stage2` and `digestSource`, the latter deriving the older digest equality through `sourceBoundary`; it is not six independent extraction assumptions. These are Result-valued equalities, and alone assert no native attempted-call trace. Safe Vec/Box operations occurring in that extracted code use the pinned Aeneas standard-library model. Authority is LOG D188 2026-10-23 16:40, C3-BIN 2026-10-23 18:05 and the 2026-10-26 native Vec/Box (a) ruling, with L8a_008 exact prints. The known rejected batch error-to-panic discrepancy is retained: accepted results/effects must agree, while rejected prefixes must both reject and count earlier reads; identical rejection error kinds are not claimed. Non-extracted wrappers and unsafe construction require the P6 route, child/source trace joins remain proof obligations, and binary correspondence is separate P7/S10 work. The D188-P2 caveat below applies. | **AeneasExtraction (D188, trace reading).** We trust the pinned Charon/Aeneas translation of each specifically associated shipped Rust body to preserve both the accepted Result and the chronological attempted digest-call sequence of its monadic extracted execution, including duplicates and every issued call before rejection; rejected prefixes must both reject, with differing non-Ok error kinds allowed as already recorded. This trace guarantee applies to the SAME body, inputs, digest replies and source/producer pins, not an arbitrary recorder or caller. `S2W_DigestExtraction.AeneasExtraction.stage1`, `stage2` and `digestSource` retain their existing kernel types; Result equality alone is not the proof of this added operational guarantee. Safe extracted Vec/Box remains under the existing Aeneas library model. LOG D188 2026-10-23 16:40 and C3-BIN's 2026-10-26 native Vec/Box and rejected-path rulings support the existing portion; the attempted-trace scope is the separate owner decision requested by L166-DECISION 2026-10-27, not prior acceptance evidence. Non-extracted wrappers, unsafe construction and actual trace association/projection consumers still need proof; no new Lean axiom, compiler equivalence or arbitrary opaque-body semantics is licensed. The D188-P2 caveat below applies. |

The rejected-path qualification comes from C3-BIN's “L166 finding and ruling;
D188 fidelity note” (2026-10-26 evening): Rust `Err(Parse)` versus extracted
`fail panic` after 10 of 12 leaf hashes. It prevents a misleading unconditional
claim of identical Result constructors on every rejection. The printed adapter
hypotheses are still exactly the existing Result-valued equalities, not silently
rewritten to weaker statements in this document.

On the left, L166 remains a Result/ordered-effects and rejected-prefix trace
association obligation; output equality does not recover an attempted-call
sequence. On the right, the scope of trusted source translation changes and
L166 must still be proved from the extracted trace and connected to the concrete
consumer. No theorem or ledger row closes by approving words. Both readings keep
P1 separate, preserve the issued-query cost (adaptive choices and rejecting
prefixes included), and neither repairs a producer from the wrong source path.''')
s=s.replace('<!-- CIa_CAVEAT -->', '''**Proposed contract caveat (applies to either D188 reading).** The selected
PublicPreparation / ExtractedTx1Model / S1 semantic-prefix cohort represents the
retired `verifier.tx1` path at five preparation interfaces whose association with
frozen release compiler input `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` is not
established: (1) `dot_type`, historical Dot sums plus count versus release sums;
(2) `prepared_claim`, scalar gamma versus a 29-element powers array;
(3) `query_geometry`, release `line_z` cache;
(4) `tx1`, retired k≤22 eight-way dispatch versus release `candidate.tx1` at
k=SPLIT with compact parsing, expansion, batched multiproofs/deferred weights
and compact checkpoint bytes; (5) retired `tx1_finish`, with no release
counterpart. The theorems remain valid about their selected model, but deployed
attribution across this semantic-prefix/preparation/query/finish boundary is
qualified until explicit association rows close against the SAME release
source and carriers. Rebuilding a historical extraction byte-identically,
compiling its adapted union, or accepting trace fidelity does not discharge
those rows. This qualification is not an attack claim and does not invalidate
the separately modelled compact/batched Op5T, multiproof, checkpoint-binding
or finish subresults within their proved domains.

Evidence and current route are [D188-PROVENANCE-FINDING, 2026-10-27](../docs/research/100bit-spend-path-20261013/design/D188-PROVENANCE-FINDING-20261027.md),
including its XRc_/XRd_ update, and
[L8a producer provenance](../evidence/l188-audit1-20261027/L8a_ProducerProvenance.md).
The selected fresh Types/Funs source hashes are respectively
`b45ee7357278642101b81933252e81f5068c937487acfdebb4f82f991c91bb83` and
`544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d`;
these are adapted producer sources, not raw release extraction or historical
object hashes. L8a initially found eight differing source cuts; D188-P2 refines
them: verifier_error is identical under release cfg, verify_observed is opaque
in both, and the five genuine interface differences above remain the caveat.
The earlier differing `prepared_new` source cut is not an added sixth interface
finding in the lead's refined list.

Reproduction recovered the historical tools, but the pinned translator fails on
six exposed release functions: `compact::check_values`, `verifier::echeck`,
`compact::expand_values`, `candidate::wide_view`, `checkpoint`, and
`prepared_claim`. The lead's route C′ extracts the remaining release path with
those six opaque leaves, handles those leaves via owned reference + Kani + Lean
correspondence, then proves the association rows. Tool trust alone supplies
neither the leaf proofs nor the cross-path associations. A translator change
and repin (route A) would need separate approval; it is not adopted here.''')
s=s.replace('<!-- CIa_SUMMARY -->', '''Approval of the reconciliation paragraphs would put the already relied-on
SDK, std, extraction, oracle, P6/P7 and logical-base scopes into one explicit
contract inventory beside the named runtime items. It would record existing
trust and its qualifications, not adopt a new theorem or remove a premise.
The historical-interface paragraph prevents accidental re-adoption of stronger
checkpoint trust. W1, the 105 UNRECORDED import-only axioms, and D188-P2 remain
visible qualifications/findings; the appendix does not waive them.

There are three separable owner decisions: (1) record the existing inventory
with its caveats; (2) select either Result or proposed trace fidelity for D188;
(3) separately consider the [ARX statement amendment](SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md).
Approving (1) does not imply (2) or (3). Trace fidelity would change the stated
operational trust scope even though it adds no kernel axiom. ARX adoption would
change the admitted-game statement; neither is an inventory correction by itself.

Before and after this job, the exact statements are unchanged:
`AspisR1.Rc10_Top.deployed` and candidate `AspisR1.ARX_Root.deployed`.
Their full kernel statements are retained in
[L8a_Rc10_Top.kernel.txt](../evidence/l188-audit1-20261027/L8a_Rc10_Top.kernel.txt)
and [L8a_ARX_Root.kernel.txt](../evidence/l188-audit1-20261027/L8a_ARX_Root.kernel.txt).
Using the ledger method (atomic conjunctive leaves and quantified law families;
shared witnesses/guards preserved; aliases not double-counted), the actual Rc10
baseline remains **83T/12P/13G/0C**, deployment-inclusive **89T/16P/13G/0C**.
Removed 0, added 0, reclassified 0. Candidate ARX's proposed 83T/11P/13G/0C and
89T/14P/13G/0C are not adopted totals or credit for this document.
L159/L185 and L181 are not removed by this job; L166 is not closed by either
wording draft. F-CONTRACT is prepared for owner review, not marked resolved;
L188 is not marked closed.

No non-vacuity theorem or joint real-byte accepted pair is constructed here.
The candidate's `ARX_Nonvacuity.conditional` still requires a complete SAME
installed accepted real-byte native pair and consistent cylinder; the checked
`JFp_SeededFixture.inhabited`, `JFp_Query00Source.source`,
`JFo_QueryFixture.inhabited`, `JFo_TX2.reader_on_saved` and
`JFo_ResumeNative.source` are partial fixture predecessors, not a complete
accepted-pair theorem. Their SAME installed extraction/runtime/game composition
is still required. The exact conditional scope remains that of the ARX amendment
and [ARX root comparison](../evidence/account-rejoin9-20261026/ARX_ROOT_COMPARISON.md#conditional-non-vacuity-and-precise-fixture-waits).
Unchanged definitions introduce no new restriction that could supply missing
non-vacuity evidence.

Frozen artifacts are inherited pins, **not freshly rebuilt**:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Validation is offline field/declaration/receipt/link reconciliation only;
**0/5 Lean attempts, 0 Kani**, no scope or build launched. No new theorem needs
an axioms print; L8a_006/007/008 prints and exact pins are reused as evidence.
No contract, ledger, Lean module, shipped file, session A candidate/worktree,
wallet or key was changed. [CIa validation and receipt](../evidence/contract-inventory1-20261027/)
record source hashes and checks. Commits are local; no push or merge.
The next deliverable is the owner's explicit inventory/D188/ARX decision and
the remaining association proofs, not a release-completion claim.''')
p.write_text(s)
