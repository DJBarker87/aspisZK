from pathlib import Path
p=Path('design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md')
s=p.read_text().replace('Inventory and contract mapping follow below. Proposed wording, the two D188\nreadings, the D188-P2 caveat and the owner decision summary are separate sections.', '''The authority is the [binding contract and owner amendment of 2026-10-26](../docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md#owner-approved-amendment-2026-10-26).
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
No recount is inferred from counting declarations.''')
s=s.replace('<!-- CIa_EXTERNAL_TABLE -->','''These supplement, rather than duplicate, the 44 projection rows.

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
strict import-wide finding.''')
p.write_text(s)
