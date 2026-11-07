# Notes for ledger26 (from TAS_)

Target not yet established. These notes are reporting instructions for the next ledger gate. They credit nothing, remove no edge and change no trust row. Sources: TCK_REPORT.md section 5, RSL_LEDGER_CLAUSES.json, ledger24 (NLX_), design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md.

## 1. Phantom-edge reclassification (wording per (az)(1); edges retained)

Record each of the following verbatim as a reclassification. The edge stays in the inventory.

> **TX2:233 → TX2:016** (`crates/aspis-core/src/field.rs::M31::to_le_bytes`, clause `call-domain:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts->crates/aspis-core/src/field.rs::M31::to_le_bytes`, required hypotheses `NCS_R050.PacketDomain`, `.PhysicalInterpretation`) and **TX2:233 → TX2:039** (`crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes`, `NCS_R073.*`): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. The frozen body (r1_pool_adapter_owned.rs:293 at 4bb3b3f51e16) calls core `u64::to_le_bytes` on `checkpoint.checkpoint_sequence : u64` (pair_forest_accounts.rs:154) as a PDA seed. It never calls a field or wide-exact `to_le_bytes`. The edge is a name-collision artifact, kept visible under the never-remove rule with this evidence. The u64 conversion is a safe std operation under ruling (au) and runs inside the parent cut, transcribed as `RSL.u64le` (RSL_Base). It is not a child row. Status of the clause: `status: RECLASSIFIED_SPURIOUS_BY_NAME`, `discharged_by: null`, `evidence: TCK_REPORT.md §5; RSL_TX2_233.lean`.

> **TX2:240 → TX2:043** (`crates/aspis-core/src/r0/domain.rs::FibreIndex::get`, clause `call-domain:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2->crates/aspis-core/src/r0/domain.rs::FibreIndex::get`, `NDT::local::NDH::04.*`): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. Line 479 is `Clock::get()` (solana_program `Sysvar::get`, imported at r1_pool_adapter.rs:45), not `FibreIndex::get`. The actual call is the Clock syscall slot (`Event.clock`/`Env.clock` in RSL_TX2_240), bound by the existing runtime row RuntimeClockSlotBinding. No trust change. Same status fields as above, `evidence: TCK_REPORT.md §5; RSL_TX2_240.lean`.

Gate rule: a RECLASSIFIED_SPURIOUS_BY_NAME clause is not an undischarged caller clause, so it does not block TX2:233/240. Under the composed-row semantics (ruling (as)) it therefore does not block 242, 241, 221, 213, TX1:333 or TX1:330 either. The canonical-callee lists of 233 and 240 keep the names, with the reclassification attached.

## 2. `discharged_by` for the NLG-upstream resume-extents clause

The clause is real, not phantom. The four ids, all `kind: native-input-upward`, `helper: TX2:124`, text "At every entered resume site, SAME original proof.length=57607 AND SAME original publicBytes.length<=1880; …":

| Clause id | Record |
|---|---|
| `NLG-upstream:TX2:241:TX2:124:native-input` | `discharged_by: "TX2:241 (internal)"`. Evidence: Ref_241 (RSL_TX2_241) reaches 064 only after `scan_proof_buffer` sets `proof_length = verifier::PROOF_BYTES` (enters as `L.scanProof`, CLOSED), `proofData.length != proofEnd → Err`, and the `publicBytes.length != STATEMENT_BYTES → Err` guard. Candidate Lean evidence: NMS_RSLDomains (branch codex/cx-tx2-owned-20261107, a72aa527f6a; not merged) derives `Dom064`'s three extents from the canonical 241 domain plus the entered-path cuts. Credit only when NMS_'s 241 root is gated. |
| `NLG-upstream:TX2:240:TX2:124:native-input` | `discharged_by: "TX2:241"` (the parent passes the clause to its child 241, which discharges it internally; 240 adds no own-input clause for it) |
| `NLG-upstream:TX2:221:TX2:124:native-input` | `discharged_by: "TX2:241"` |
| `NLG-upstream:TX2:213:TX2:124:native-input` | `discharged_by: "TX2:241"` |

Status of each stays OPEN until the TX2:241 root is CLOSED in the same gate. The gate then sets `status: DISCHARGED`, with `discharged_by` resolving to that root's Lean name. Root0, the fourth 064 input, is NOT covered by this clause. It stays with G1 (section 4).

## 3. RuntimeClockSlotBinding consumer (addition only)

Append to the row's Consumer text, with the statement unchanged:

> Also consumed at programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:479 (`Clock::get()` in `owned::stage2`), the deployed TX2 route (r1_pool_adapter.rs:945–962 `mod owned; use owned::{stage1, stage2}`). The previously listed r1_pool_adapter.rs:910 is the non-owned validate copy. (Addition, TCK_REPORT.md §5; no change to the statement or removal condition.)

The row status is unchanged (ADDED-LEAD-20261105). This is a reporting correction, not a new trust item.

## 4. Recording the non-row top-composition obligations

The ledger counts rows: functions with an obligation, a root and CLOSED/OPEN status. The following are top-composition obligations. They are not rows, are not in the 599 count, and must never change the CLOSED/OPEN row totals. Record them in a separate section `top_composition_obligations`, one record each:

| id | What | Owner | TAS interface field | Closure condition |
|---|---|---|---|---|
| TOP:G1a | Root0-free weak law of actual TX2:064 (+ write-free, Ok ⇒ header) | NNC_ | `NNC_G1a` | Lean root of `Refines064 V0 f064 (fun _ _ => True) w` plus `writeFree`/`okHeader`, standard axioms |
| TOP:G1b | 241/240 (and 221/213) proved library-parametric | NMS_, NMV_; 221/213 unowned (W-RSL) | `NMS_Roots.r241`, `NMV_Roots.r240`, `NMW_Roots` | the row roots have the TAS parametric type (checked by `rfl` at the host) |
| TOP:G1c | NMF′ (Root0 or charged event from native facts) | NNC_ | `NNC_NMFPrime` | Lean root, no headline call, no `accepted2` |
| TOP:R0rep | native Root0 = canonical `V0.Root0` on the TX2 entry payloads | NNC_ | `NNC_R0Rep` | Lean root |
| TOP:CaseSplit | NMF′ event = headline event at native1 := model | NNC_ | `NNC_CaseSplit` | `rfl`-level lemma |
| TOP:G2 | Root0-free write frame of the weak 240 reference | NMV_ | `NMV_Roots.g2` | Lean root |
| TOP:A0 | `extraction` at native := model (digestSource under the exhibited `missing`) | G0 final job | `A0_Digest` | host term |
| TOP:A1 / TOP:A2 | RSL Ref ≡ AdapterRw model (returned arms, at `EnvRep`), op10/op11, `missing` exhibited | NND_ | `NND_A1`, `NND_A2`, `Sig.Exhibited` | Lean roots per definition pair (NND_INVENTORY) |
| TOP:A3 / TOP:A4 / TOP:A5 | stage wrappers → D189 `first`/`second`; entry dispatch → game (d); entry-state rep, incl. allocator association (gap ALLOC) | NNE_ | `NNE_A3`, `NNE_A4`, `NNE_A5`, `NNE_EntryRep`, `Sig` rep fields | Lean roots; ALLOC escalated if it needs trust |
| TOP:W-RSL | RSL-form library-parametric 221/333 and 213/330 folds | unowned | `NMW_Roots` | Lean roots with native cuts |
| TOP:G0 | the top assembly | G0 final job | `RSL.TAS.top` instantiated on the host | TAS_WIRING.md section 5 checklist passed, including the statement and non-vacuity audits |

Each record should carry `status` (OPEN / CANDIDATE / CLOSED), the Lean name once delivered, the commit, its `#print axioms` and `consumes_trust: []`, unless a record genuinely needs a trust row. None is expected; ALLOC is the one to watch, and an owner decision applies there. A row's CLOSED status does not depend on these obligations. The headline's closure does: report "headline composed" only when TOP:G0 is CLOSED, and keep reporting "target not yet established" until then.

Rows 330/333 and 213/221 are the same functions. Their RSL Props are identical (`TAS.row330_is_213`, `TAS.row333_is_221`, both `rfl`), so one root closes each pair, as RSL_INDEX already states.
