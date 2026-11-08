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
| `RuntimeEntrypointAdmission-Pool` (same seven fields as AdapterRw.RuntimeEntrypointAdmission, at the Pool program entrypoint) | Solana runtime entrypoint deserialization, Pool program | **ADDED-LEAD-20261107** | C3-BIN ruling (ap); owner decision 2026-11-04 (lead may add runtime rows of the same class); initial heap validity/alias/counter facts only; no CPI frame, token-program behaviour or success |
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

## Lead additions under the standing delegation, 2026-11-04: two runtime rows ADDED, pending owner confirmation

Both rows were ADDED by the lead (C3-BIN rulings (ab) and (ac)), reported to the owner as additions, never as removals or reclassifications. The owner may reject either; the dependent slice S root then returns to OPEN. Neither is consumed by privacy (Stream B D598 for (ab)).

| Surface | Currently named contract item | Status | Authority and exact scope |
|---|---|---|---|
| set_return_data / get_return_data semantics (emit_result; Pool readback) | RuntimeReturnData (ruling (ab), 2026-11-04) | **ACCEPTED (owner 2026-11-04)** | C3-BIN 'Lead rulings (aa) and (ab), 2026-11-04'. A set_return_data(b) by program P followed by the caller's get_return_data() in the same instruction context with no intervening CPI returns Some((P, b)) exactly, b within the runtime maximum. Native side must prove exact bytes at the model trace position and no later set; Pool side must prove immediate readback and program-id check separately. One CLOSED native use: emit_result (NFD_, merged f2a33ab0963). Scope clarified by ruling (ab'), 2026-11-04: nonempty replies only (1 <= len(b) <= 1024; SDK getter returns None at length 0); Pool consumer is pair_forest_dispatch.rs (792 bytes); Pool-side association OPEN (NFO_). |
| sol_memcmp_ syscall at the scan_proof_buffer 688-byte compare (wrapper 0x1749d0 in both release ELFs) | RuntimeMemcmp (ruling (ac), 2026-11-04) | **ACCEPTED (owner 2026-11-04)** | C3-BIN 'Lead ruling (ac), 2026-11-04'; NFH_COMPARISON_FINDING.md. For the SAME two valid readable 688-byte ranges, normal return into the supplied i32 slot, zero iff all 688 bytes equal, no other observable effect; no ordering, sign or timing property. Native certificate must prove exact SAME buffers and length 688 passed and only the slot tested for zero; Lean uses the 688-only completion, never NFD_'s universal law verbatim. No CLOSED use yet (NFJ_ running). Trust-reduction route: outside-slice packet on the pinned validator implementation; not commissioned. |

### RuntimeClockSlotBinding (ADDED-LEAD-20261105, under the owner decision of 2026-11-04 on Solana runtime assumptions)

Statement: for the same instruction execution context, `clockGet ctx = ok v -> v = bankSlot ctx` (the Clock sysvar's slot, when the call succeeds, is the bank slot of the executing transaction). Says nothing about success of the call, slot monotonicity, epochs or account retention. Consumer: programs/r1-cost-probe/src/r1_pool_adapter.rs:910 (Clock::get()?.slot) and every forwarded current_slot. Source: evidence/exp-premises-20261105/NGP_CANDIDATE_ROWS.md (NGP-R1). Removal condition: a proved realization of the pinned Clock sysvar implementation. Ruling (aj).

### ReviewedTranscription-prepared_claim (ruling (ah), ADDED-LEAD-20261106; reclassification, option A)

Row TX1:193 crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim is CLOSED under ruling (ah) because Aeneas rejects its loop (Not_found at loop join). Trusted beyond the emitted-body route: the hand transcription of the prefix-owned reference f_ref into Lean (evidence/prepared-claim2-20261105/NGY_TRANSCRIPTION.md, line-by-line correspondence), with the frozen function proved equal to f_ref by Kani proof_for_contract with the Dot child as a logging oracle and a corruption control (NGY_ASSOCIATION.md, NGY_STUBS.md). Removal condition: an emitted body for prepared_claim from the pinned extractor (or an approved successor) proved equal to the transcription.

### ReviewedTranscription-queries_from_pairs (ruling (ah), ADDED-LEAD-20261106; reclassification, option A)

Row TX1:168 crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries is CLOSED under ruling (ah) because Aeneas rejects the loop of aspis-core r0_transcript::queries_from_pairs (Not_found at loop join; evidence/aeneas-loops-20261105). Trusted beyond the emitted-body route: the reviewed transcription of the reference (evidence/transcript-queries3-20261106/NHK_TRANSCRIPTION.md, with the NHA_ outlined reference emission and the Query31 interfaces as corroboration), with the frozen function tied to it by per-length membership harnesses, window splits, a native word/block loop association and matched controls (NHK_ASSOCIATION.md, NHK_MEMBERSHIP.md). The event schedule (NGQ_EVENTS.md) matches the model; no ordering assumption is added. Removal condition: an emitted body for queries_from_pairs from the pinned extractor (or an approved successor) proved equal to the transcription.

### ReviewedTranscription-POOL324 (ruling (ah), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:324 programs/aspis-pool/src/pair_forest.rs::pool_v1_pair_forest_global_root_v1 (frozen body sha256 782c5b73…) is CLOSED as PCG_GlobalLaw.row_324 using source fission. Substitution: seven pool_v1_tree_parent calls -> parent_window(log); harness pair K072/K073. The child call(s) are replaced in the fission copy by a local logging window that receives the same arguments. PCG_ASSOCIATIONS.json mechanically checks that the copy equals the frozen body after whitespace and optional trailing commas, once the listed name substitutions are applied. Kani runs on the fission copy with matched failing controls; it does not run on the frozen function itself. Trusted beyond the emitted-body route: the claim that this textual substitution preserves the frozen body's behaviour. Removal condition: a native certificate on the actual frozen function (for example under the (bi)(3) cut-point pattern once adopted), proved equal to the same reference. Evidence: evidence/pc-helpers2-20261110 (merged research 7143c06d3da), PCG_CERTIFICATES.md, PCG_CORRESPONDENCE.md. Ruling (ah) and Stream C review of PCG_.

### ReviewedTranscription-POOL345 (ruling (ah), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:345 programs/aspis-pool/src/pair_forest_dispatch.rs::SolanaPairForestVerifierRuntimeV1::get_return_data (frozen body sha256 c11d47ef…) is CLOSED as PCG_ReturnBridge.row_345 using source fission. Substitution: program::get_return_data() -> reply_window(log); the actual function is also run on fixed None/Some replies K066/K068; harness pair K070/K071. The child call(s) are replaced in the fission copy by a local logging window that receives the same arguments. PCG_ASSOCIATIONS.json mechanically checks that the copy equals the frozen body after whitespace and optional trailing commas, once the listed name substitutions are applied. Kani runs on the fission copy with matched failing controls; it does not run on the frozen function itself. Trusted beyond the emitted-body route: the claim that this textual substitution preserves the frozen body's behaviour. Removal condition: a native certificate on the actual frozen function (for example under the (bi)(3) cut-point pattern once adopted), proved equal to the same reference. Evidence: evidence/pc-helpers2-20261110 (merged research 7143c06d3da), PCG_CERTIFICATES.md, PCG_CORRESPONDENCE.md. Ruling (ah) and Stream C review of PCG_.

### ReviewedTranscription-POOL296 (ruling (ah), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:296 programs/aspis-pool/src/nullifier.rs::pool_v1_pair_forest_marker_seed_v1 (frozen body sha256 7e6d2a27…) is CLOSED as PCG_MarkerSeed.row_296 using source fission. Substitution: solana_program::hash::hashv -> hash_window, pack_pool_v1_pair_forest_marker_seed_v1 -> pack_window (log); hash values via RuntimeSha256Value only; harness pair K095/K096. The child call(s) are replaced in the fission copy by a local logging window that receives the same arguments. PCG_ASSOCIATIONS.json mechanically checks that the copy equals the frozen body after whitespace and optional trailing commas, once the listed name substitutions are applied. Kani runs on the fission copy with matched failing controls; it does not run on the frozen function itself. Trusted beyond the emitted-body route: the claim that this textual substitution preserves the frozen body's behaviour. Removal condition: a native certificate on the actual frozen function (for example under the (bi)(3) cut-point pattern once adopted), proved equal to the same reference. Evidence: evidence/pc-helpers2-20261110 (merged research 7143c06d3da), PCG_CERTIFICATES.md, PCG_CORRESPONDENCE.md. Ruling (ah) and Stream C review of PCG_.

### ReviewedTranscription-POOL320 (ruling (ah)/(ay)(3), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:320 programs/aspis-pool/src/pair_forest.rs::next_pair_forest_lane_v1 is CLOSED as PCD_Row320.result_state_effects (PCD-RT-POOL320). Aeneas failed on the structured frozen body (E006/E007), which establishes (ay)(2) eligibility. The whole-loop composition is transcribed by hand from three extracted primitives (E002) through a generic loop induction (PCD_LaneBridge.result_state_effects). Native source-ordered segments with matched failing controls are K021/K022, K025/K026, K039/K040, K041/K042 and K027/K028. Trusted beyond the emitted-body route: the hand composition of the loop into the frozen body's order. Removal condition: an emitted body for next_pair_forest_lane_v1 from the pinned extractor (or an approved successor) proved equal to the composition. Evidence: evidence/pc-terminal-children1-20261110 (PCD_CLOSED.json, PCD_SOURCE_COVERAGE.json, PCD_CORRESPONDENCE.md).

### ReviewedTranscription-POOL223 (ruling (ah)/(ay)(3), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:223 crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::PoolV1PairLeafWitnessV1::validate is CLOSED as PCI_ValidatePacket.full. The native evidence runs on a mechanically diffed fission of the frozen body (fission sha256 3229f4b5...): each field multiplication is replaced by a logging window, and the any-loop over second_commitment is cut to its prefix plus one arbitrary iteration. PCI_validate_associate.py checks the fission against the frozen body after named erasure and rejects error-constructor and product-operand mutants. Native windows K021/K024/K026/K028 pass; their controls K022/K023/K025/K027/K029/K030 fail. No multiplication stub is admitted. Lean bridges each emitted multiply (PCI_Mul.value), derives each reached operand domain from the same witness, and proves the loop by induction (PCI_ValidateScan). Trusted beyond the emitted-body route: that the fission's windows are the frozen body's calls in order. Removal condition: an emitted body for validate from the pinned extractor (or an approved successor) proved equal to the composition. Evidence: evidence/pc-deposit-children2-20261110 (PCI_ASSOCIATIONS.json, PCI_CORRESPONDENCE.md, PCI_CLOSED.json).

### ReviewedTranscription-POOL332 (ruling (ah)/(ay)(3), ADDED-LEAD-20261110, Stream C; reclassification, option A)

Row POOL:332 programs/aspis-pool/src/pair_forest.rs::require_exact_account_count is CLOSED as PCI_CountState.complete. The native evidence runs on a fission (sha256 37d5da9e...) whose only change replaces accounts.len() with a usize parameter; the body reads no account. PCI_associate.py checks the whole frozen body after whitespace and rejects comparison and error-arm mutants. K006/K008/K010 pass over the full usize pair domain; K007/K009/K011 fail. The relation accountCount = accounts.length is the representation of the same own slice under Stream C ruling (c-c), not a child result. Trusted beyond the emitted-body route: the single len substitution. Removal condition: a native harness on the unmodified body over all slice lengths, or an emitted body proved equal. Evidence: evidence/pc-deposit-children2-20261110 (PCI_ASSOCIATIONS.json, PCI_CORRESPONDENCE.md, PCI_CLOSED.json).

### RuntimeReturnDataClear (ADDED-LEAD-20261106, under the owner decision of 2026-11-04 on Solana runtime assumptions)

Statement: within one instruction execution, a successful `set_return_data` call with an empty slice leaves the return-data register such that a subsequent `get_return_data` observes no return data until a later `set_return_data`; nothing is assumed about other programs, failure of the call, or persistence across instructions. Consumer: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs stage2's empty return-data clear before the verifier result is emitted. Companion of RuntimeReturnData (nonempty 1..1024), which it does not extend. Source: evidence/slice-d-entry2-20261106 (NHD_) and slice-d-entry3-20261106 (NHJ_REMAINING.md, stage2 row). Removal condition: a proved realization of the pinned runtime's return-data register. Ruling (am).

### RuntimeCpiAccountView (ADDED-LEAD-20261110, Stream C, under the owner decision of 2026-11-04 on Solana runtime assumptions)

Statement: for one invoke/invoke_signed by the Pool that RETURNS to the Pool, with instruction account metas M: (1) every admitted account whose key is not in M has the same data bytes (including length), lamports and owner in the caller's view after the return as immediately before the call; (2) for every key in M that is also in the passed AccountInfo list, the caller's view after the return of its data bytes, lamports and owner equals the callee's final value for that key, and nothing else is said about that value. Not covered: token- or system-program semantics, success of any CPI, what a callee does to the accounts it receives, readonly-on-entry (RuntimeCpiReadonlyEntry7 stays PENDING and unused), rent, rollback, stack height, key/flag/handle/Rc stability, RefCell borrow-counter preservation, return data (RuntimeReturnData). Key exclusion becomes cell exclusion only through RuntimeEntrypointAdmission-Pool plus the source's require_unique_accounts at the same accounts; the native bridge must prove the exact M and passed infos. Consumers: Pool CPI sites in POOL:328 (deposit token transfer, system creation) and POOL:330/POOL:348 (terminal verifier and withdrawal CPIs). Basis: Agave cpi.rs caller/callee account update. Soundness-side only; not in the privacy trust list. No CLOSED use yet. Removal condition: a proved realization of the deployed runtime's CPI account update. Ruling: C3-BIN 'Stream C ruling (c-a), 2026-11-10'.

### ReviewedTranscription-TX1:344 (ruling (bn), ADDED-LEAD-20261107; reclassification, option A)

Row TX1:344 programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 (frozen revision 4bb3b3f51e16) is to be certified by source fission: a prefix-owned copy in which snapshot (try_borrow_data and data.to_vec), stage1_owned, try_borrow_mut_data and copy_from_slice are replaced by calls on an explicit log/window parameter receiving the same arguments, mechanically checked equal to the frozen body after whitespace normalisation and the listed name substitutions. Trusted beyond the emitted-body route: the claim that this textual substitution preserves the frozen body's behaviour. Removal condition: a native certificate on the actual frozen function proved equal to the same fold. Pinned Aeneas cannot emit the frozen body (RefCell guard drop, ruling (be)(2)).

USED (lead, 2026-11-08; ledger29, evidence/ledger29-20261111, NNM_, gate PASS 594/0/5 at branch tip 93207b7791e): row TX1:344 is CLOSED as `AspisR1.NNG_Candidate344.candidate` (NMV objects from NNG_WrapperR4_objects only, RSL rev4 statement), so this item is now consumed by a CLOSED row. The source fission and the mechanical copy equality (NMV_fission.py, NMV_ASSOCIATIONS.json) and the K063/K064 parent-call mutant controls were independently rechecked by the gate (NNM_CANDIDATE_REVIEW.json, NNM_WRAPPER_REVIEW.json). The credit lists this row in `consumes_trust`, with the SDK borrow law, the std item and the extraction item narrowed by (bc). Transitive consumers to be added when credited: the TX1:333/TX2:221 and TX1:330/TX2:213 instantiations (ledger30). Statement, class and removal condition unchanged. ReviewedTranscription-TX2:240 remains unused.

### ReviewedTranscription-TX2:240 (ruling (bn), ADDED-LEAD-20261107; reclassification, option A)

Row TX2:240 programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 (frozen revision 4bb3b3f51e16) is to be certified by source fission: as for TX1:344, with set_return_data(&[]), the seven snapshots, Clock::get() and stage2_owned replaced by log/window calls receiving the same arguments; the window laws are the SDK borrow law ((be)(2)), the std item ((au)), RuntimeReturnDataClear and RuntimeClockSlotBinding (deployed consumer r1_pool_adapter_owned.rs:479). Trusted beyond the emitted-body route: the claim that this textual substitution preserves the frozen body's behaviour. Removal condition: a native certificate on the actual frozen function proved equal to the same fold.

### ReviewedTranscription-TX2:217 (ruling (ah), ADDED-LEAD-20261107; reclassification, option A)

Row TX2:217 programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release (frozen 4bb3b3f51e16) is CLOSED in ledger27 under ruling (ah): the pinned Aeneas rejects the frozen body (loop-context collapse), so the model side is the NCV_ safe-Rust reference (evidence/native-decref-20261028), extracted by the pinned tools and proved against RowSpec_217 rev3 for every lane length (NMX_R3_DecoderFold.root); the native side is Kani proof_for_contract of the ACTUAL frozen decoder against that reference, split by length, with loop rule B and the ruling (t)/(br) controls (evidence/tx2-auth-20261111, tx2-217-controls-20261111). Trusted beyond the emitted-body route: the hand reference as the faithful transcription of the decoder's intended behaviour, tied to the actual code only through the Kani contract. Removal condition: an emitted body of the frozen decoder proved equal to the same fold.

Addition to RuntimeClockSlotBinding (lead, 2026-11-08; TGB-4, addition only): the deployed TX2 consumer is programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:479 (owned::stage2, Clock::get()), in addition to the previously listed r1_pool_adapter.rs:910 copy. On the deployed path the Clock sysvar read either returns the slot or returns an Err whose payload construction may allocate; that Err arm is covered by this row as a runtime reply (no new trust class), and an allocation failure there is an abort carrying only its event prefix under (bl)(3). The row's statement is otherwise unchanged.
