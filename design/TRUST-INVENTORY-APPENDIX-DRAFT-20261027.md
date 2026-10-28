# Trust inventory appendix — 27 October 2026

**APPROVED by the owner 2026-10-27 and incorporated into the binding contract (SECURITY-CONTRACT-20261021.md, "Owner-approved amendment, 2026-10-27"). The draft text below is retained verbatim; where it says "not adopted" or "candidate", the contract amendment controls. For the trust inventory, the TRACE-fidelity D188 column was selected.**

This appendix proposes a literal inventory for the binding security contract.
It changes no proof, premise ledger, implementation, artifact or accepted trust.
The deployed 100-bit target is not yet established. ARX remains a candidate.

## Sources, status and counting

The authority is the [binding contract and owner amendment of 2026-10-26](../docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md#owner-approved-amendment-2026-10-26).
The fresh [L8a audit](../evidence/l188-audit1-20261027/L8a_TrustAudit.md),
[field map](../evidence/l188-audit1-20261027/L8a_TrustFieldMap.json),
[exact kernel types](../evidence/l188-audit1-20261027/L8a_structure.json), and
[per-declaration classification](../evidence/l188-audit1-20261027/L8a_SurfaceClassification.json)
identify the selected RPz8 Rc10/ARX closure. These are reused evidence, not a new replay.
Acceptance citations refer to [C3-BIN](../docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md),
[LOG](../docs/research/v8-r0-zk-20261009/LOG.md) and the
[2026-10-26 TRUST-AUDIT release trust table](TRUST-AUDIT-20261026.md#release-trust-table).
C3-BIN's 2026-10-27 “l188-audit1 … F-CONTRACT” addendum adopts the audit's
reconciliation finding, not new trust or ARX adoption.

**NAMED-IN-CONTRACT** means the item is literally named in the current contract;
it does not mean its individual fields are enumerated there.
**ACCEPTED-ELSEWHERE** means the cited dated ruling already accepts the stated
scope, while the contract lacks its literal item. **UNRECORDED** means no
acceptance is inferred and the surface remains a finding, not proposed new trust.
† marks historical interfaces recognized in earlier rulings: acceptance of their
conditional use is not permission to assume their deployment instance. Seven
such fields are retained for exhaustive indexing, not added to today's trust base.

The 44 fields comprise 15 SDK, 9 admission, 7 historical checkpoint, 6 extraction,
3 std, 2 allocator, 1 P1 and 1 syscall fields. The older extraction interface is
derived by `S2W_DigestExtraction.sourceBoundary`; it is not three extra independent
trust assumptions. Two admissions and repeated SDK uses explain why this field
count differs from the inherited ledger's 83 actual T / 89 deployment-inclusive T.
No recount is inferred from counting declarations.

## One-to-one named-field inventory

| Exact projection (one row per field) | Contract item now | Status | Dated authority / limit |
|---|---|---|---|
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.counterZero` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.duplicateKeysShareCell` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.freshGuards` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.liveAccount` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.noExternalBorrows` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.sharedCellsOnlyEqualKeys` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.AdapterRw.RuntimeEntrypointAdmission.valid` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; LOG D189; initial heap validity/alias/counter facts only |
| `AspisR1.Port1_Library.TrustedStd.option_ok_or` | No literal item; TrustedStd | **ACCEPTED-ELSEWHERE** | LOG D157 2026-10-22 08:35; C3-BIN 2026-10-23 18:05 and 2026-10-25 late; pure Option/Result interpretation; deployment library item, not fresh top proof dependency |
| `AspisR1.Port1_Library.TrustedStd.result_unwrap32` | No literal item; TrustedStd | **ACCEPTED-ELSEWHERE** | LOG D157 2026-10-22 08:35; C3-BIN 2026-10-23 18:05 and 2026-10-25 late; pure Option/Result interpretation; deployment library item, not fresh top proof dependency |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.account_data_cell` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.borrow_frame` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.cell_counter` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.cell_payload` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.error_move_drop` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.exclusive_deref` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.exclusive_drop` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.exclusive_err` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.exclusive_ok` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.guard_liveness` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.guard_move` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.shared_deref` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.shared_drop` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.shared_err` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2Trust.S2TrustedSdkBorrow.shared_ok` | No literal item; S2TrustedSdkBorrow | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 01:20; LOG D189 (D189 2026-10-23 17:35); accepted fifteen-field SDK/RefCell interpretation; no caller result |
| `AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding.history` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; history wrapper, not a second runtime trust item |
| `AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission.entry` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | same runtime admission + LOG D189; wrapper entry and related; nested entry fields are listed separately |
| `AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission.related` | RuntimeEntrypointAdmission (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | same runtime admission + LOG D189; wrapper entry and related; nested entry fields are listed separately |
| `AspisR1.S2W_D189Wrappers.Allocator.allocate` | Allocator (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; data-only allocate/cleanup interface; no success or account-access proposition |
| `AspisR1.S2W_D189Wrappers.Allocator.cleanup` | Allocator (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | C3-BIN 2026-10-23 02:40/18:05; data-only allocate/cleanup interface; no success or account-access proposition |
| `AspisR1.S2W_DigestExtraction.AeneasExtraction.digestSource` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; C3-BIN 2026-10-26 native Vec/Box ruling; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; source extraction association; not SBF equivalence; provenance finding D188-P below |
| `AspisR1.S2W_DigestExtraction.AeneasExtraction.stage1` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; C3-BIN 2026-10-26 native Vec/Box ruling; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; source extraction association; not SBF equivalence; provenance finding D188-P below |
| `AspisR1.S2W_DigestExtraction.AeneasExtraction.stage2` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; C3-BIN 2026-10-26 native Vec/Box ruling; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; source extraction association; not SBF equivalence; provenance finding D188-P below |
| `AspisR1.S2W_ExtractionBoundary.AeneasExtraction.digest` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; S2W_DigestExtraction.sourceBoundary; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; older three-field derived interface, not independent additional trust |
| `AspisR1.S2W_ExtractionBoundary.AeneasExtraction.stage1` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; S2W_DigestExtraction.sourceBoundary; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; older three-field derived interface, not independent additional trust |
| `AspisR1.S2W_ExtractionBoundary.AeneasExtraction.stage2` | No literal item; AeneasExtraction | **ACCEPTED-ELSEWHERE** | LOG D188; S2W_DigestExtraction.sourceBoundary; D188 2026-10-23 16:40; native Vec/Box ruling 2026-10-26; older three-field derived interface, not independent additional trust |
| `AspisR1.S2W_ExtractionBoundary.P1.realization` | No literal item; P1 | **ACCEPTED-ELSEWHERE** | existing P1; C3-BIN 2026-10-23 11:05/18:05; ideal-oracle realization, not a proof that SHA is random |
| `AspisR1.S2W_ExtractionBoundary.RuntimeSyscall.returningValue` | RuntimeSyscall (§3, 2026-10-26) | **NAMED-IN-CONTRACT** | existing P3; C3-BIN 2026-10-23 11:05/18:05; successful hash return only; no termination/totality premise |
| `AspisR1.S2W_TrustedStd.TrustedStd.slice_copy_from_slice` | No literal item; TrustedStd | **ACCEPTED-ELSEWHERE** | LOG D157; C3-BIN 2026-10-23 18:05; slice copy only; W1 total abstract-domain versus valid native references remains |
| `AspisR1.S2X.CheckpointVersionBinding.events` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |
| `AspisR1.S2X.CheckpointVersionBinding.key` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |
| `AspisR1.S2X.CheckpointVersionBinding.ledger` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |
| `AspisR1.S2X.CheckpointVersionBinding.loadedAtEntry` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |
| `AspisR1.S2X.CheckpointVersionBinding.noInterveningWrite` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |
| `AspisR1.S2X.CheckpointVersionBinding.savedAtCommit` | No literal item; historical checkpoint interface | **ACCEPTED-ELSEWHERE†** | TRUST-AUDIT 2026-10-26 historical-interface row; C3-BIN 2026-10-23 11:05/18:05; owner amendment 2026-10-26 supersedes independent history trust; not a new adopted top-level trust item; replaced by data persistence + game + source proofs |

## Definition-level and external surfaces

These supplement, rather than duplicate, the 44 projection rows.

| Surface | Currently named contract item | Status | Authority and exact scope |
|---|---|---|---|
| `AspisR1.CPR_DataPersistence.TwoTransactionLaw` (definition) | RuntimePersistence | **NAMED-IN-CONTRACT** | Owner amendment 2026-10-26 §3; adjacent ordinary-key data-only law; zero lamports absent. The older `CPR_Persistence.TwoTransactionLaw` full-image candidate is not adopted. |
| P6 / Kani shipped-to-owned-reference association, L190 | None literally named | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-23 02:40; LOG D188 2026-10-23 16:40; C3-BIN 2026-10-25 late §4 and 2026-10-26 native Vec/Box (b). Exact Result, effects and contents correspondence must actually be certified; no free Lean P6 trust field. |
| P7 compiler/LLVM/platform and release-pinned library base, L189 | None literally named | **ACCEPTED-ELSEWHERE** | C3-BIN 2026-10-25 late §4 and 2026-10-26 coherent-replay scope ruling; LOG D188 separates source extraction from deployed binary association. Applies to exact selected pins, not arbitrary compiler/source changes. |
| frozen3 security/oracle model, L194 | frozen3 headline and failure/work contract | **NAMED-IN-CONTRACT** | Owner amendment 2026-10-26 §1; same target and charged collision branch. No additional cryptographic assumption inferred from this inventory. P1 is separately indexed above. |
| Game a–d; wrapper success antecedents | Two-transaction game §2 | **NAMED-IN-CONTRACT** (G, not external trust) | Owner amendment 2026-10-26 §2; TRUST-AUDIT G classification. Eleven expanded game clauses plus two success antecedents; no silent restriction on adaptive submissions. |
| `propext`, `Classical.choice`, `Quot.sound` | No literal axiom list | **ACCEPTED-ELSEWHERE** | Job rules r1p-common §3 / local-lean §4, reaffirmed for this job 2026-10-27; TRUST-AUDIT 2026-10-26 and L8a clean audit 2026-10-27. Exactly the reachable axiom set for both tops; not operational assumptions. |
| Each of 105 nonstandard imported axiom declarations | None; not approved security premises | **UNRECORDED** (F-AXIOM) | One exact row per declaration in [CIa_UnrecordedAxioms.tsv](../evidence/contract-inventory1-20261027/CIa_UnrecordedAxioms.tsv), linked to L8a's exact classification. All unreachable from both top kernel traversals; 84 formatter and 21 other infrastructure/Aeneas names. Import-wide standard-only still fails. |
| Each of 8,565 pinned library implementation surfaces | P7 / D188 base, not literal contract list | **ACCEPTED-ELSEWHERE** (pinned implementation base only) | C3-BIN 2026-10-25 late §4; 2026-10-26 replay-scope ruling. Exact names and per-root reachability are in L8a_SurfaceClassification.json. `opaque`/`partial`/`extern`/`implemented_by` flags do not themselves add a logical axiom; no blanket acceptance of external templates. |
| Each of 551 repository implementation surfaces | No independent trust item | **UNRECORDED** as independent trust; no adoption proposed | All unreachable in both tops, per the exact 551 rows of L8a_SurfaceClassification.json. Logical values are kernel checked. A compiler-generated unsafe implementation is not its logical definition; no trust finding about a reachable theorem is manufactured from this flag. |
| Unsafe MaybeUninit/uninit/raw-write source association; child joins, source-event traces, slot installations | None as trust | **UNRECORDED** as trust; retained proof obligations | C3-BIN 2026-10-25 late §4 and 2026-10-26 native Vec/Box (b) explicitly require proof. `ClaimsUnrolledFinish.StdCalls`, `NP6_StdModel.Reservation` and `MultiproofConeP6Frozen2Stage.P6Boundary` are not certificates of unsafe native equivalence. |

The complete declaration table is incorporated by exact name from the linked
L8a classification, not replaced by a new assumption per flag. Its disjoint
counts are 8,565 + 551 + 105 + 3 = 9,224. All 105 unrecorded axioms are
individually retained in the companion TSV so none disappear into P7/D188.
The 551 unreachable repository implementation flags are not 551 extra T rows.
This distinction preserves both the kernel dependency pass and the unresolved
strict import-wide finding.

## Proposed contract paragraphs

Each paragraph below is proposed text for recording an already authorized scope.
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
supersedes that status, not its narrow law or its source-association caveats.

## D188 alternatives — separate owner decision

These are alternative replacement paragraphs, not cumulative permissions.
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
prefixes included), and neither repairs a producer from the wrong source path.

## D188-P2 contract caveat

**Proposed contract caveat (applies to either D188 reading).** The selected
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
and repin (route A) would need separate approval; it is not adopted here.

## Owner summary and unchanged result

Approval of the reconciliation paragraphs would put the already relied-on
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
the remaining association proofs, not a release-completion claim.

## Status note (lead, 2026-10-27 15:30 UTC): D188 contradicted for one body

Finding D188-P3 (docs/research/100bit-spend-path-20261013/design/
D188-PROVENANCE-FINDING-20261027.md) shows the pinned emission of
`sampler::low_base_p_digits` drops a write the frozen Rust performs. The D188
row does not credit that body. Credit for multiproof::verify_in_place,
verifier::update_residue_row, sampler::add_small_base_p and
BatchedWeights::finish is suspended pending per-function checks. Repair route:
owner decision, D188-FIDELITY-DECISION-20261027.md (recommended: narrow D188
and bridge those bodies natively as opaque leaves). The inventory text above is
otherwise unchanged.

## Owner-approved clarification, 2026-10-28 (amendment fifth): native contract semantic transport

Clarifies the existing P6 (Kani) and D188/AeneasExtraction (Charon/Aeneas) tool trust; it is not a new kind of trust. Text: "Native contract semantic transport (result projection). For only the frozen owned TX1 stage1, owned TX2 stage2 and SolanaDigest wrapper bodies, reference bodies, operation dictionaries, features, input/outcome encodings and tool versions enumerated by the accepted receipts, we trust that the Rust execution interpreted by Kani/CBMC and the reference execution interpreted by pinned Charon/Aeneas denote the same Rust language/primitive semantics under the certified common external world. We trust the explicitly recorded association of those Rust entries with the Lean function parameters native1/native2, of the digest wrapper with installed ops.op43, and of the external digest with hashv." Source: evidence/native-topspec-20261028/NCQ_TOPSPEC.md. Uses are reported as reclassification of the `extraction` premise, never as removal. FixturePdaRuntime (evidence/joint-pda-20261028/JHs_TRUST_PROPOSAL.md) is DEFERRED and not adopted.

## Lead decision under the standing delegation, 2026-10-28 late: FixturePdaRuntime ADOPTED (non-vacuity only)

Text as in evidence/joint-pda-20261028/JHs_TRUST_PROPOSAL.md: for the seven enumerated fixture PDA invocations, sol_create_program_address agrees with the guarded JHs_PDA.derive model (the SHA value comes from the existing runtime SHA row, and the curve check is the pinned curve25519-dalek 4.1.3 decompression). Scope: the concrete joint non-vacuity witness (JHw_Joint.source) ONLY. It is never used by the soundness theorem, which quantifies op38 under ruling (s). Kind: a runtime-behaviour row of the same kind as the existing RuntimeSyscall/SHA row. The seven off-curve facts are PROVED (JHt_OffCurve) and the seven digest equations are PROVED (JHs_), so the row covers only the syscall-equals-documented-algorithm correspondence.
