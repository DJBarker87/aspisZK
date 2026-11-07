## Task section for the ledger26 Codex job: top-assembly items (from TAS_)

Target not yet established. This section replaces TAS_LEDGER_NOTES.md, which stays in the tree as the historical version. It tells the ledger26 gate how to record what has happened since ledger25 (NMQ_, 582 CLOSED / 0 QUALIFIED / 17 OPEN of 599). The section credits nothing by itself, removes no edge, and changes no trust row except the two lead additions under ruling (bn), which are recorded here as already decided. Sources:
- C3-BIN-20261021.md, rulings (bk) to (bo) and the owner decision of 2026-11-07;
- RSL_REVISION2.md;
- top-assembly-20261107/rev2/REV2_IMPACT.md;
- TCK_REPORT.md section 5;
- the NNC_, NNE_, NNF_ and NMV_ handoffs;
- design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md.

### 1. Specification revision (RSL rev2)

1. Record that the canonical RowSpecs are RSL Revision 2 (evidence/rowspec-lead-20261107 at be66076856e; frozen source 4bb3b3f51e16 unchanged). Revision 2 adds allocation-abort arms at named sites, and nothing else:
   - the String clone in the owned getters (`RS.ofCloned`);
   - the decoder Box sites before a later Err (`S1Lib.decodeReachesAlloc`);
   - the `format!` in `lib.rs::error` (`mapVErr`).
   Domains, trust rows and the metric are unchanged.
2. Rows whose Ref changed directly: TX1:345, TX1:328, TX2:241, TX2:242, TX2:233, TX2:234. Rows that inherit the change only: TX1:344, TX1:333, TX1:330, TX2:240, TX2:221, TX2:213. Unchanged: TX2:217, TX1:136, TX1:137, TX1:087, TX1:094.
3. A root is admissible for a row in this gate only if its statement is the rev2 `RowSpec_X`. Check it with `example : <root type> = RSL.<row>.RowSpec_X … := rfl` against the rev2 sources. A root proved against Revision 1 for a changed or inheriting row is not credited until it is re-checked against rev2.
4. Record the superseded claim verbatim as SUPERSEDED (reporting and proof correction, not a protocol change): "Revision 1 `TX1_328.rejects_silent` rejected every event-free outcome at k ≠ 10, including the constant abort". It is replaced by `rejects_silentRet` and `ref_admits_abort`. An abort writes nothing and accepts nothing.
5. Merged-module repairs. These are proof-only, with statements unchanged (REV2_IMPACT.md):
   - NMV_NoWritePool, NMV_NoWriteOwned and NMV_NoWrite241 take NMV_REV2_NOWRITE.patch (compiled locally against rev2);
   - NNC_RSLReads and NNC_RSLAuth take the replacement lines in TAS_G0_BRIEF.md section 5.

   A root that depends on an unrepaired module is not credited. Record the old and new source hashes for each repaired module.

### 2. Trust rows under ruling (bn): additions in the existing class

Add these two rows verbatim, in the existing ReviewedTranscription class, as a reclassification under option A. Nothing is removed.

| Row | Statement | Consumer | Removal condition | Status |
|---|---|---|---|---|
| ReviewedTranscription-TX1:344 | The listed textual substitution in the source-fission copy of `r1_pool_adapter_owned.rs::stage1` (each SDK/std/child call site replaced by a call on an explicit log/window parameter with the same arguments, checked equal to the frozen body after whitespace normalisation and the listed name substitutions; NMV_fission.py, NMV_ASSOCIATIONS.json, fission sha256 9824c8ffc6be3668c642a83d3a899f8faff78506b514c595a2c57c9deb3aebbf) preserves the frozen body's behaviour. | TX1:344 root `NMV_CandidateRoots.root344` / `NMV_TasRoots.field344` | a native certificate on the actual frozen function | ADDED-LEAD-20261107 (ruling (bn)) |
| ReviewedTranscription-TX2:240 | The same, for `…::stage2`. | TX2:240 root `NMV_CandidateRoots.root240` / `NMV_TasRoots.field240` | the same | ADDED-LEAD-20261107 (ruling (bn)) |

A TX1:344 or TX2:240 credit lists its row in `consumes_trust`. The SDK borrow law, std item and runtime rows (RuntimeClockSlotBinding, RuntimeReturnDataClear) that the window laws use are already carried, and stay unchanged.

### 3. Ruling (bo) and the owner decision: statement items, not trust

1. **(bo) allocator instantiation.** Record it as an instantiation of the top statement: `A := Bool`, `allocator := abortIndicator`, `state1 = final1 = state2 = final2 := true`. It is not a hypothesis and not trust. Its correspondence is proved by NNE_ (NNE_AbortIndicator, NNE_AllocatorNecessary). No allocator-success row exists or is added.
2. **Owner decision of 2026-11-07: split top form, option B with Realizes.** Record the adopted top statement verbatim from C3-BIN, together with its five binding conditions. The adopted shape is `C5num ∧ (the other ten conjuncts, unchanged) ∧ (Outcome(…, bad := E_rec) ∨ E_rec)`, under the retained binders plus `realizes`, with the pair instantiated from the adversary's execution. Mark the earlier shapes as superseded, not removed:
   - TAS `Bound ∧ (Concl ∨ Event)`;
   - TFM `top_split` with E_head;
   - EVB `top_splitB` with the inner `bad := E_head`.

   Record that numbers, range (`maxQueries`) and trust are unchanged, and that E_rec is charged once. Option A remains a fallback only if B fails.
3. **RZ-STATE (open item for the owner, not a row).** Record verbatim: "Realizes defines state1/state2 as the adversary's outputs while (bo) fixes them to true; ART_PartialAccount.firstSyntax/secondSyntax pass the state to the model wrapper; at worlds where the adversary outputs false, Realizes-by-rfl and RecSelect cannot both hold. Lead recommendation: treat the state as part of the (bo) instantiation through the state-normalised adversary a⊤ (TAS_G0_BRIEF.md section 6); owner approval required." Status OPEN-OWNER. It blocks TOP:G0, and no row.

### 4. Phantom-edge reclassification (wording per (az)(1); edges retained)

Record each of the following verbatim as a reclassification. The edge stays in the inventory.

> **TX2:233 → TX2:016** (`crates/aspis-core/src/field.rs::M31::to_le_bytes`, clause `call-domain:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts->crates/aspis-core/src/field.rs::M31::to_le_bytes`, required hypotheses `NCS_R050.PacketDomain`, `.PhysicalInterpretation`) and **TX2:233 → TX2:039** (`crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes`, `NCS_R073.*`): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. The frozen body (r1_pool_adapter_owned.rs:293 at 4bb3b3f51e16) calls core `u64::to_le_bytes` on `checkpoint.checkpoint_sequence : u64` (pair_forest_accounts.rs:154) as a PDA seed. It never calls a field or wide-exact `to_le_bytes`. The edge is a name-collision artifact, kept visible under the never-remove rule with this evidence. The u64 conversion is a safe std operation under ruling (au) and runs inside the parent cut, transcribed as `RSL.u64le` (RSL_Base). It is not a child row. `status: RECLASSIFIED_SPURIOUS_BY_NAME`, `discharged_by: null`, `evidence: TCK_REPORT.md §5; RSL_TX2_233.lean`.

> **TX2:240 → TX2:043** (`crates/aspis-core/src/r0/domain.rs::FibreIndex::get`, clause `call-domain:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2->crates/aspis-core/src/r0/domain.rs::FibreIndex::get`, `NDT::local::NDH::04.*`): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. Line 479 is `Clock::get()` (solana_program `Sysvar::get`, imported at r1_pool_adapter.rs:45), not `FibreIndex::get`. The actual call is the Clock syscall slot (`Event.clock`/`Env.clock` in RSL_TX2_240; window `NMV_WindowClock` in the fission copy), bound by the existing runtime row RuntimeClockSlotBinding. No trust change. Same status fields, `evidence: TCK_REPORT.md §5; RSL_TX2_240.lean`.

Gate rule: a RECLASSIFIED_SPURIOUS_BY_NAME clause is not an undischarged caller clause. It does not block TX2:233 or TX2:240, nor, under ruling (as), 242, 241, 221, 213, TX1:333 or TX1:330. The canonical-callee lists of 233 and 240 keep the names, with the reclassification attached.

### 5. `discharged_by` for the NLG-upstream resume-extents clause

The clause is real, not phantom. It has four ids, all `kind: native-input-upward`, `helper: TX2:124`, with text "At every entered resume site, SAME original proof.length=57607 AND SAME original publicBytes.length<=1880; …".

| Clause id | Record |
|---|---|
| `NLG-upstream:TX2:241:TX2:124:native-input` | `discharged_by: "TX2:241 (internal)"`. Ref_241 (rev2 RSL_TX2_241) reaches 064 only after `scan_proof_buffer` sets `proof_length = verifier::PROOF_BYTES` (enters as `L.scanProof`, CLOSED), the `proofData.length != proofEnd → Err` guard and the `publicBytes.length != STATEMENT_BYTES → Err` guard. Candidate Lean evidence: NMS_'s 241 domain derivation (`Dom064`'s three extents from the canonical 241 domain plus the entered-path cuts), at NMS_'s rev2 commit. |
| `NLG-upstream:TX2:240:TX2:124:native-input` | `discharged_by: "TX2:241"`. The parent passes the clause to its child 241, which discharges it internally. NMV_'s `root240` derives Domain241 internally (NMV_CANDIDATE_PACKET.md), and 240 adds no own-input clause. |
| `NLG-upstream:TX2:221:TX2:124:native-input` | `discharged_by: "TX2:241"` |
| `NLG-upstream:TX2:213:TX2:124:native-input` | `discharged_by: "TX2:241"` |

Each stays OPEN until the TX2:241 root is CLOSED in the same gate. The gate then sets `status: DISCHARGED`, with `discharged_by` resolving to that root's Lean name. Root0, the fourth 064 input, is not covered by this clause. It stays with TOP:G1c-B and TOP:R0rep (section 8).

### 6. RuntimeClockSlotBinding consumer (addition only)

Append to the row's Consumer text, with the statement unchanged:

> Also consumed at programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:479 (`Clock::get()` in `owned::stage2`), the deployed TX2 route (r1_pool_adapter.rs:945–962 `mod owned; use owned::{stage1, stage2}`). The previously listed r1_pool_adapter.rs:910 is the non-owned validate copy. In the formal chain it is consumed by NNE_Clock (`child_argument` forwards the same reply; `success` applies the row only on Ok) and by the (bn) window NMV_WindowClock. (Addition, TCK_REPORT.md §5 and NNE_WIRING.md; no change to the statement or removal condition.)

The row status is unchanged (ADDED-LEAD-20261105). This is a reporting correction, not a new trust item.

### 7. Crediting rows whose roots are instantiated parameterized folds

Under (bd)(3), (be)(1) and (bm)(2)(d), an OPEN child enters its parent's root as a RowSpec parameter, and the parent's root is emitted by instantiation when the child closes. Apply these rules in this gate:

1. **Leaf first.** A row is CLOSED only if its root, after instantiation, has no RowSpec parameter left. Instantiate bottom-up along the spines: 136 → 137 → 087 → 094 → 328 → 345 → 344, then 217 and 234 → 233 → 242 → 241 → 240, then 344 and 240 → 333/221 → 330/213.
2. **Same constant, same arguments.** Each child parameter must be filled by a CLOSED root of the same Lean constant that the parent's interpreter calls, at the same arguments. Check this by `rfl` on the `Impl` field, for example `(NMV_TasRoots.implementation I a1 a2).f345 = I.f345` (`NMV_TasRoots.children_same`) and `NNF_TAS.install` keeping f344/f240. A child stated over a different representation needs the (bm)(2)(c) equality proof first.
3. **The instantiation is the root.** The credited root is the instantiated term, for example `NMV_CandidateRoots.root344 VL P C a1 (I.f345) NMT_345.root`. It must:
   - be compiled in the gate's combined import;
   - pass a raw ax2 walk of that term, standard axioms only;
   - keep `consumes_trust` as the union of the fold's and the children's rows (for 344 and 240, add the section 2 rows).
4. **Extra parameters block credit.** A fold may carry parameters beyond child RowSpecs, such as library installation boundaries or representation obligations. Examples: `NMV_TasRoots.packet`'s `pl : PoolLaws L`; the `Allocation` arguments `a1 a2`, which are universally quantified and therefore fine; `NNC_*.assemble`'s `nativeRep`, `headerRep` and `selected`. Such a fold is credited only if each extra parameter is either universally quantified in the row's own statement, as a genuine input, or filled by a CLOSED term. Otherwise the row stays OPEN, with status `CANDIDATE-FOLD` and fields `pending_children` and `pending_parameters` naming each one. Never credit by treating a parameter as a hypothesis of the row.
5. **Same-function pairs.** TX1:333/TX2:221 and TX1:330/TX2:213 are one function each, and their Props are definitionally equal (`TAS.row333_is_221`, `TAS.row330_is_213`). One instantiated root closes both members of a pair. Each member still needs both wrapper packets, because `NNF_Folds.process_*` take RowSpec_344 and RowSpec_240.
6. **(as) composed semantics.** A parent whose children are all CLOSED by instantiation, and whose own clauses are discharged, is CLOSED. Its credit is reported as composed, with the children's root names listed. A child's CLOSED status never depends on its parent.
7. **Current merged state.** These folds exist and are ready for instantiation:
   - NMV_ 344/240: `NMV_CandidateRoots.root344`/`root240`, which need the canonical 345/241 roots and `pl`.
   - NNF_ 333/221/330/213: `NNF_Folds.process_tx1/process_tx2/entry_tx1/entry_tx2`, `NNF_TAS.roots`, which need the 344 and 240 roots.

   NMT_ (345) and NMS_ (241/242) have no rev2 candidate at the time of writing. So unless those land in this gate, 344, 240, 333, 221, 330 and 213 stay OPEN as CANDIDATE-FOLD. Gap W-RSL from TAS_LEDGER_NOTES is now delivered as folds by NNF_.

### 8. Top-composition obligations (not rows)

The ledger counts rows: functions with an obligation, a root and a CLOSED/OPEN status. The items below are top-composition obligations. They are not in the 599, and they must never change the CLOSED/QUALIFIED/OPEN row totals. Record them in a separate section `top_composition_obligations`, one record each, with these fields:
- `id`, `what`, `owner`;
- `interface_field` (the TAS/TFM/EVB/TASB structure field);
- `deliverable` (Lean name and commit, or null);
- `extra_parameters`;
- `status`: OPEN, CANDIDATE (the term exists but has unfilled extra parameters), CLOSED (a closed term of exactly the field type, raw ax2 standard-only), SUPERSEDED or OPEN-OWNER;
- `print_axioms`;
- `consumes_trust`, normally `[]`.

| id | What | Owner | Interface field | Current status |
|---|---|---|---|---|
| TOP:G1a | Root0-free weak law of the actual TX2:064, plus writeFree and okHeader | NNC_ | `TAS.NNC_G1a` | CANDIDATE: `NNC_G1a.assemble`; pending `nativeRep`, `headerRep` |
| TOP:G1b | 241/240 and 221/213 parametric in the library | NMS_, NMV_, NNF_ | `NMS_Roots.r241`, `NMV_Roots.r240`, `NMW_Roots` | NMV_/NNF_ parts CANDIDATE-FOLD (`NMV_TasRoots.field240`, `NNF_TAS.roots`); 241 OPEN |
| TOP:NMF_B | NMF′-B: Root0 at the selected occurrence, or E_rec, from Root0-free facts plus SelectsPair | NNC_ (resumed for B) | `EVB.NNC_NMFPrimeB` | OPEN (B amendment pending; selector generalisation per EVB_REPORT §2.2) |
| TOP:CaseSplit | NMF′ event = headline E_head | NNC_ | `TAS.NNC_CaseSplit` | SUPERSEDED by the owner decision (B re-targets both events); retained, not removed |
| TOP:RecSelect | Realizes plus TX1 facts ⇒ SelectsPair | unassigned | `EVB.RecSelect` | OPEN (blocked on RZ-STATE) |
| TOP:HeadlineB | Outcome with `bad := E_rec` (FJv_DRelease.remove′, FJv_DNativeAccepted copy) | unassigned | `EVB.HeadlineB` | OPEN |
| TOP:Split | `concl_iff` (reassociation) and `rest` (Root0-free non-Outcome conjuncts) | G0 or unassigned | `TFM.Split` | OPEN |
| TOP:R0rep | native Root0 = canonical `V0.Root0` on the TX2 entry payloads | NNC_ | `TAS.NNC_R0Rep` | CANDIDATE: `NNC_R0Rep.assemble`; pending `selected` |
| TOP:G2 | Root0-free write frame of the weak 240 reference | NMV_ | `NMV_Roots.g2` | CANDIDATE: `NMV_TasRoots.packet`.g2; pending `pl : PoolLaws L` (CLOSED scan226, reconstruct224, encode165, emit219 installation); rev2 repair patch required |
| TOP:A0 | `extraction` at native := model | G0 | `TAS.A0_Digest` | OPEN |
| TOP:A1 / TOP:A2 | rev2 RSL 345/241 Ref returned arms ≡ AdapterRw model at `EnvRep`, and `missing` exhibited | NND_ | `TAS.NND_A1`, `TAS.NND_A2`, `Sig.Exhibited` | OPEN (running; must target the rev2 Refs) |
| TOP:A3 / TOP:A4 / TOP:A5 | stage wrappers → D189 first/second; entry → game (d); entry-state representation; allocator per (bo) | NNE_ | `TAS.NNE_A3/A4/A5` | CANDIDATE: `NNE_RecordSig.a3/a4/a5` at `NNE_RecordSig.physical S0 d r`; pending the host `S0` and A1/A2 |
| TOP:EntryRep | selected routes | NNE_ | counts route `TAS_TopB_NNE.top_splitB_counts` | CLOSED at stand-in level (local compile); host instantiation with G0 |
| TOP:PoolLaws | the four CLOSED Pool library effect laws as `NMV_NoWrite.PoolLaws L` | G0 | parameter of `NMV_TasRoots.packet` | OPEN |
| TOP:RZ-STATE | state coherence between Realizes and (bo) | owner (via lead) | `ExecB.realizes_mk` / `RecSelect` | OPEN-OWNER |
| TOP:AVG | averaged deployed bound, E_rec charged once, over every H, no conditioning | G0 | `TASB.deployed_charge` (host form via `F3U_Averaging.charge`) | OPEN; compiled at stand-in level |
| TOP:G0 | final host assembly of the split-B top | G0 | `TASB.top_splitB_physical` instantiated | OPEN; brief at TAS_G0_BRIEF.md |

A row's CLOSED status never depends on these obligations. The headline's closure does. Report "headline composed" only when TOP:G0 is CLOSED and its gate has passed: raw ax2 on the new top, NFX scan, combined import, statement audit and non-vacuity. Until then, keep reporting "target not yet established".

### 9. Other lines to carry

- **Extraction provenance.** Carry the (bk) status line verbatim from ledger25, and recompute the conservative impact against the ledger26 CLOSED set by the same lexical method. Do not reopen any row for provenance.
- **K086 / (aj)(a).** Still PENDING. Carry ledger25's entry unchanged.
- **Unchanged.** Frozen3, the L154 statement parameter, narrowed D188, 100-bit per-attempt soundness, privacy and the two-transaction contract are all unchanged.
