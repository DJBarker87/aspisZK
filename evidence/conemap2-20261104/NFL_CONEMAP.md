# NFL cone map refresh — 4 November 2026

**Numbers are status, not new credit. Target not yet established.**

This is a mapping over existing receipts; no Lean, Kani, Rust, extraction, native build, cold replay or fresh axioms audit ran. NFK has **219 CLOSED / 2 QUALIFIED / 366 OPEN of 587 occurrences**, not 219 discharged theorem premises. Q: **126/149 CLOSED, 2 QUALIFIED, 21 OPEN; 0/2 roots CLOSED**. S: **97/97 CLOSED; 7/7 roots CLOSED conditional on added (ab)/(ac) trust pending owner confirmation**. Unique functions and repeated TX occurrences are distinct units; overlapping assignments are never added to the global total.

The canonical [map](../../design/S1-S10-CLOSURE-MAP-20261026.md) defines subjects. Its initial Rc7 matrix is followed by Rc8/Rc9/Rc10 appendices on the SAME date; **Rc10 is the last superseding 2026-10-26 status**, including S6's historical scoped closure. [Rc7 inventory](../recount7-20261026/Rc7_premises.json) supplies the requested expanded row IDs; its retained list must not be mistaken for the later Rc10 retained list. This report preserves historical retirements, and grants no new retirement. The ledger frozen Rust revision is `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; NFK source revision is `9905ea55a106eadbf120088a8b7601c6fa7c2843`. Historical proofs are not silently reassigned to this Rust revision.

[Row mapping](NFL_ROW_TO_CONE.json) records every occurrence, status, body hash, exact anchor or directed canonical call path, reason, slice membership, trust rows and support receipt references. [Builder](NFL_build.py) uses exact function IDs, not names resembling cone titles. Subject anchors are selected from canonical obligations and frozen inventory domains (not discovery search hits). Directed paths stay within TX1/TX2 and preserve the ledger's conservative target alternatives. Recursive/overapproximated graph membership is dependency coverage, not a semantic/refinement proof. S2 dispatch and S6 TX1 intentionally have broad descendant counts; **counts include their prerequisites**, distinguished from subject anchors. All source sites fall under S10; that does not supply its missing artifact/release obligations.

The [premise crosswalk](NFL_PREMISE_COVERAGE.json) exhausts all **32 raw Rc7 P rows**, including alias L185 and distinct native/global quantifier domains. It records candidate function sites and their status without asserting equivalence of a function packet to a full premise. No newly CLOSED ledger row is claimed to discharge an Rc7 Lnnn/Nnnn/F3Y_G_ family. Already-retired N and L primitive/preparation families receive support overlap only. In particular F3Y_G_ rows are P, not trust; local/native and global world/submission/Evidence domains stay distinct.

## Ten-cone matrix

The four columns retain the canonical 2026-10-26 format. Occurrence counts are **total / CLOSED / QUALIFIED / OPEN** and overlap across cones.

| Cone and canonical obligation | Exact ledger families | Discharging theorem / evidence and remaining boundary | Status |
|---|---|---|---|
| **S1** preparation/transcript driver, Prepared/claim/scratch binding | Retired N001–N046, N108–N115; L122–L124/L126/L129–L132/L139–L141/L168 | **220 / 46 / 0 / 174** occurrences. Historical: `SAP_PrepareOwner.installed; SAP_Binding.prepare; F3Y_InstalledLaws.prepare; SAP_SaveOnRun.saved; TxS_Encoding.model; SAF_AcceptedValue.value`. SAME accepted preparation laws remain historically retired; the three native subject roots in this later occurrence ledger are OPEN. No contradiction: the domains and status units differ. Full caller/refinement and shared deployment gates remain. | **CLOSED for historical accepted preparation families**; no change from final Rc10 status. |
| **S2** dispatcher/adapter/header, same native caller and physical history | L159 (alias L185), L166, L181; retired dispatcher/header N117/N118 and L088–L099/L155–L158/L160–L165/L180/L182–L184 | **579 / 219 / 2 / 358** occurrences. Historical: `Rc7_Native.accepted; Rc7_Top.deployed; Rc10_Top.deployed (conditional consumers, not retained-row discharges)`. Source-local entry/adapter composition is OPEN. Close StoredCarrierBinding, exact accepted Result/effects plus rejected-prefix reads and whole oracle experiment/history association. Slice result bytes do not associate Pool return data. | **OPEN; adopted portions TRUST**; no change from final Rc10 status. |
| **S3** row/group/Weights::pair | L133–L138/L142/L144–L146 and corresponding F3Y_G_ families; retired N047–N074 | **205 / 63 / 0 / 142** occurrences. Historical: `F3Y_InstalledLaws.primitives; FIs_OnRun.strengthen/FIs_Finish.strengthen (historical rounds only)`. Native/global L142/L144–L146 remain after historical round retirements. Weights::pair and semantic subject cuts are OPEN outside both slices. Need exact dual-fold pair and semantic initial/chain/masked terminal laws on their full, distinct domains. | **OPEN**; no change from final Rc10 status. |
| **S4** four dots | L143 and F3Y_G_L143; retired N047–N088/L148 support | **50 / 42 / 0 / 8** occurrences. Historical: `Installed primitive support; historical FIp concrete query installation, without matching-family discharge`. Both four_dots roots remain OPEN in Q. CLOSED decode/reducer/new/finish helpers do not cover Dot::push and the SAME-view all22 matching equations; native/global L143 remain. | **OPEN**; no change from final Rc10 status. |
| **S5** strict decode/tower/pairing/dot kernels | L133–L138/L142/L147 and corresponding F3Y_G_ families; retired N052–N069/N075–N079/L110–L121/L125/L127/L128/L148 | **88 / 57 / 0 / 31** occurrences. Historical: `FGm_Aligned.values; FGm_Join.accepted_raw_join_or_collision; FIs_OnRun.strengthen; FIs_Finish.strengthen`. L142 native/global Pair remains. Historical FIs round/final-dot retirements are reused; Q arithmetic helpers do not complete Pair, reached operands, source-machine/state and caller interpretation. | **OPEN**; no change from final Rc10 status. |
| **S6** decoder/public/TX1/checkpoint, including forest/Claims | L176 historically retired at Rc8; retired L091–L093/L099/L149/L150/L165/L171–L175/L177/L179/N115 | **393 / 162 / 1 / 230** occurrences. Historical: `S6N_Installation.facts/accepted; S6N_Decoder.complete; S6N_Getters.complete`. Preserve scoped S6N retirement. Slice S adds conditional source-path coverage, not a new retirement; TX1 driver, checkpoint and resume occurrence subjects remain OPEN. Full deployed closure still needs same runtime bytes/history, ownership/errors/adoption and trust-instance association. | **CLOSED for historical listed accepted families under retained trust**; no change from final Rc10 status. |
| **S7** query values/geometry/inverses/batched accumulation and matching | L143/F3Y_G_L143; shared L159/L166/L181; retired N047–N107/L149/L150/L169/L170 | **156 / 126 / 2 / 28** occurrences. Historical: `F3Y_InstalledLaws.primitives/canonical/domain/multiply/one/inverse; Rc4_Assemble.deployed (historical primitive support)`. Q has 0/2 CLOSED roots: query_loop OPEN and QueryGeometry::for_range QUALIFIED in both TXs. Need coherent retarget replay for geometry qualification, caller composition of remaining query functions, native/global matching and shared deployment association. | **OPEN**; no change from final Rc10 status. |
| **S8** accumulator/residue/compact finish; shared parser/multiproof joins | L147/F3Y_G_L147 historically retired by Rc10; shared L159/L166/L181; retired L100–L109/L149/L150/L170/L173/L195–L199 | **35 / 23 / 0 / 12** occurrences. Historical: `P6C_Extension.boundary/source_preserved; P6C_FullBoundary.same_cuts; FIs_OnRun.strengthen/FIs_Finish.strengthen`. Two residue-update occurrences are CLOSED in Q, while Accumulator::new, compact checking/expansion and finish_query_dot remain OPEN outside slices. Historical dot-family retirement does not close this later native occurrence coverage. Shared full batch/runtime/oracle gates remain. | **OPEN at deployment boundary**; no change from final Rc10 status. |
| **S9** factored Libra weights | L142/L144–L146 plus round L133–L138 and corresponding F3Y_G_ families; retired N070–N074 | **26 / 23 / 0 / 3** occurrences. Historical: `Installed semiring/primitive support and accepted finish transport only; no new exact FunctionalWeights instance`. Factored root TX2:133 is OPEN outside Q/S. CLOSED generic field operations do not instantiate FunctionalWeights, dual-fold pair or masked terminal equations; L142/L144–L146 native/global remain. | **OPEN**; no change from final Rc10 status. |
| **S10** all source sites and continuations, including errors; artifact correspondence | L166/L181 and historically L176; L187/L188; L186 accepted retirement; P7/P6 TRUST | **587 / 219 / 2 / 366** occurrences. Historical: `Low2_source_to_elf_manifest.json/Low2_final_receipt.json (accepted L186 retirement under P7); Rc10 conditional source joins`. 366 OPEN and 2 QUALIFIED sites remain. Need complete source/error/ownership/oracle continuation coverage and coherent final dependency replay L187 plus final axioms/trust/adoption/artifact association audit L188. No new artifact correspondence/rebuild here. | **OPEN; lowering subrow historically CLOSED**; no change from final Rc10 status. |

## Per-cone assessment

Historical retirement support below is reused from the canonical dated appendices and [Rc10_059 receipt](../recount10-20261026/Rc10_059/receipt.json), with its stored #print axioms results. This is not a fresh check of those theorems or their complete statements. The audit does not claim a new theorem closure. The historical receipt's standard axioms are propext, Classical.choice and Quot.sound; its focused check is not L187/L188 completion.

### S1 — preparation/transcript driver, Prepared/claim/scratch binding

Occurrences: 220 total, 46 CLOSED, 0 QUALIFIED, 174 OPEN; 51 intersect Q/S. Subject anchors: TX1:087, TX1:179, TX1:193; anchor statuses {"OPEN": 3}. Anchors inside Q/S: none.

Family boundary: Retired N001–N046, N108–N115; L122–L124/L126/L129–L132/L139–L141/L168. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: none specific to these historically retired families. Historical accepted P retirements, separately reused: none. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `SAP_PrepareOwner.installed; SAP_Binding.prepare; F3Y_InstalledLaws.prepare; SAP_SaveOnRun.saved; TxS_Encoding.model; SAF_AcceptedValue.value`. **Status change from the final 2026-10-26 Rc10 table: none.** SAME accepted preparation laws remain historically retired; the three native subject roots in this later occurrence ledger are OPEN. No contradiction: the domains and status units differ. Full caller/refinement and shared deployment gates remain.

### S2 — dispatcher/adapter/header, same native caller and physical history

Occurrences: 579 total, 219 CLOSED, 2 QUALIFIED, 358 OPEN; 242 intersect Q/S. Subject anchors: TX1:086, TX1:094, TX1:330, TX1:331, TX1:333, TX1:344, TX1:345, TX2:057, TX2:064, TX2:065, TX2:213, TX2:214, TX2:221, TX2:240, TX2:241; anchor statuses {"OPEN": 15}. Anchors inside Q/S: none.

Family boundary: L159 (alias L185), L166, L181; retired dispatcher/header N117/N118 and L088–L099/L155–L158/L160–L165/L180/L182–L184. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L159, L166, L181. Historical accepted P retirements, separately reused: none. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `Rc7_Native.accepted; Rc7_Top.deployed; Rc10_Top.deployed (conditional consumers, not retained-row discharges)`. **Status change from the final 2026-10-26 Rc10 table: none.** Source-local entry/adapter composition is OPEN. Close StoredCarrierBinding, exact accepted Result/effects plus rejected-prefix reads and whole oracle experiment/history association. Slice result bytes do not associate Pool return data.

### S3 — row/group/Weights::pair

Occurrences: 205 total, 63 CLOSED, 0 QUALIFIED, 142 OPEN; 69 intersect Q/S. Subject anchors: TX1:132, TX1:134, TX1:136, TX2:129; anchor statuses {"OPEN": 4}. Anchors inside Q/S: none.

Family boundary: L133–L138/L142/L144–L146 and corresponding F3Y_G_ families; retired N047–N074. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L142, L144, L145, L146, F3Y_G_L142, F3Y_G_L144, F3Y_G_L145, F3Y_G_L146. Historical accepted P retirements, separately reused: L133, L134, L135, L136, L137, L138, F3Y_G_L133, F3Y_G_L134, F3Y_G_L135, F3Y_G_L136, F3Y_G_L137, F3Y_G_L138. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `F3Y_InstalledLaws.primitives; FIs_OnRun.strengthen/FIs_Finish.strengthen (historical rounds only)`. **Status change from the final 2026-10-26 Rc10 table: none.** Native/global L142/L144–L146 remain after historical round retirements. Weights::pair and semantic subject cuts are OPEN outside both slices. Need exact dual-fold pair and semantic initial/chain/masked terminal laws on their full, distinct domains.

### S4 — four dots

Occurrences: 50 total, 42 CLOSED, 0 QUALIFIED, 8 OPEN; 50 intersect Q/S. Subject anchors: TX1:104, TX2:070; anchor statuses {"OPEN": 2}. Anchors inside Q/S: TX1:104, TX2:070.

Family boundary: L143 and F3Y_G_L143; retired N047–N088/L148 support. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L143, F3Y_G_L143. Historical accepted P retirements, separately reused: none. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `Installed primitive support; historical FIp concrete query installation, without matching-family discharge`. **Status change from the final 2026-10-26 Rc10 table: none.** Both four_dots roots remain OPEN in Q. CLOSED decode/reducer/new/finish helpers do not cover Dot::push and the SAME-view all22 matching equations; native/global L143 remain.

### S5 — strict decode/tower/pairing/dot kernels

Occurrences: 88 total, 57 CLOSED, 0 QUALIFIED, 31 OPEN; 62 intersect Q/S. Subject anchors: TX1:003, TX1:015, TX1:026, TX1:106, TX1:107, TX1:108, TX1:109, TX1:110, TX1:111, TX1:116, TX2:003, TX2:011, TX2:019, TX2:072, TX2:073, TX2:074, TX2:075, TX2:076, TX2:077, TX2:082, TX2:115, TX2:116; anchor statuses {"CLOSED": 16, "OPEN": 6}. Anchors inside Q/S: TX1:003, TX1:015, TX1:026, TX1:106, TX1:107, TX1:108, TX1:109, TX1:110, TX1:111, TX1:116, TX2:003, TX2:011, TX2:019, TX2:072, TX2:073, TX2:074, TX2:075, TX2:076, TX2:077, TX2:082.

Family boundary: L133–L138/L142/L147 and corresponding F3Y_G_ families; retired N052–N069/N075–N079/L110–L121/L125/L127/L128/L148. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L142, F3Y_G_L142. Historical accepted P retirements, separately reused: L133, L134, L135, L136, L137, L138, L147, F3Y_G_L133, F3Y_G_L134, F3Y_G_L135, F3Y_G_L136, F3Y_G_L137, F3Y_G_L138, F3Y_G_L147. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `FGm_Aligned.values; FGm_Join.accepted_raw_join_or_collision; FIs_OnRun.strengthen; FIs_Finish.strengthen`. **Status change from the final 2026-10-26 Rc10 table: none.** L142 native/global Pair remains. Historical FIs round/final-dot retirements are reused; Q arithmetic helpers do not complete Pair, reached operands, source-machine/state and caller interpretation.

### S6 — decoder/public/TX1/checkpoint, including forest/Claims

Occurrences: 393 total, 162 CLOSED, 1 QUALIFIED, 230 OPEN; 177 intersect Q/S. Subject anchors: TX1:094, TX1:186, TX1:276, TX1:332, TX2:124, TX2:163, TX2:165, TX2:169, TX2:219, TX2:224, TX2:226; anchor statuses {"CLOSED": 8, "OPEN": 3}. Anchors inside Q/S: TX1:276, TX1:332, TX2:163, TX2:165, TX2:169, TX2:219, TX2:224, TX2:226.

Family boundary: L176 historically retired at Rc8; retired L091–L093/L099/L149/L150/L165/L171–L175/L177/L179/N115. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: none specific to these historically retired families. Historical accepted P retirements, separately reused: L176. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `S6N_Installation.facts/accepted; S6N_Decoder.complete; S6N_Getters.complete`. **Status change from the final 2026-10-26 Rc10 table: none.** Preserve scoped S6N retirement. Slice S adds conditional source-path coverage, not a new retirement; TX1 driver, checkpoint and resume occurrence subjects remain OPEN. Full deployed closure still needs same runtime bytes/history, ownership/errors/adoption and trust-instance association.

Compared with the *initial* Rc7 matrix, L176/S6 had already changed at Rc8 via S6N, before this slice refresh. That accepted historical change is not slice-earned credit. The retained S6 CLOSED label is restricted to the accepted families and dictionary of that historical theorem, not every source/error site in NFK.

### S7 — query values/geometry/inverses/batched accumulation and matching

Occurrences: 156 total, 126 CLOSED, 2 QUALIFIED, 28 OPEN; 148 intersect Q/S. Subject anchors: TX1:088, TX1:175, TX1:176, TX1:178, TX1:181, TX2:058, TX2:099, TX2:100, TX2:102, TX2:104; anchor statuses {"OPEN": 8, "QUALIFIED": 2}. Anchors inside Q/S: TX1:088, TX1:181, TX2:058, TX2:104.

Family boundary: L143/F3Y_G_L143; shared L159/L166/L181; retired N047–N107/L149/L150/L169/L170. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L143, L159, L166, L181, F3Y_G_L143. Historical accepted P retirements, separately reused: none. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `F3Y_InstalledLaws.primitives/canonical/domain/multiply/one/inverse; Rc4_Assemble.deployed (historical primitive support)`. **Status change from the final 2026-10-26 Rc10 table: none.** Q has 0/2 CLOSED roots: query_loop OPEN and QueryGeometry::for_range QUALIFIED in both TXs. Need coherent retarget replay for geometry qualification, caller composition of remaining query functions, native/global matching and shared deployment association.

### S8 — accumulator/residue/compact finish; shared parser/multiproof joins

Occurrences: 35 total, 23 CLOSED, 0 QUALIFIED, 12 OPEN; 25 intersect Q/S. Subject anchors: TX1:096, TX1:097, TX1:098, TX1:099, TX1:174, TX1:195, TX2:114, TX2:125; anchor statuses {"CLOSED": 2, "OPEN": 6}. Anchors inside Q/S: TX1:195, TX2:125.

Family boundary: L147/F3Y_G_L147 historically retired by Rc10; shared L159/L166/L181; retired L100–L109/L149/L150/L170/L173/L195–L199. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L159, L166, L181. Historical accepted P retirements, separately reused: L147, F3Y_G_L147. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `P6C_Extension.boundary/source_preserved; P6C_FullBoundary.same_cuts; FIs_OnRun.strengthen/FIs_Finish.strengthen`. **Status change from the final 2026-10-26 Rc10 table: none.** Two residue-update occurrences are CLOSED in Q, while Accumulator::new, compact checking/expansion and finish_query_dot remain OPEN outside slices. Historical dot-family retirement does not close this later native occurrence coverage. Shared full batch/runtime/oracle gates remain.

### S9 — factored Libra weights

Occurrences: 26 total, 23 CLOSED, 0 QUALIFIED, 3 OPEN; 24 intersect Q/S. Subject anchors: TX2:133; anchor statuses {"OPEN": 1}. Anchors inside Q/S: none.

Family boundary: L142/L144–L146 plus round L133–L138 and corresponding F3Y_G_ families; retired N070–N074. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L142, L144, L145, L146, F3Y_G_L142, F3Y_G_L144, F3Y_G_L145, F3Y_G_L146. Historical accepted P retirements, separately reused: L133, L134, L135, L136, L137, L138, F3Y_G_L133, F3Y_G_L134, F3Y_G_L135, F3Y_G_L136, F3Y_G_L137, F3Y_G_L138. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `Installed semiring/primitive support and accepted finish transport only; no new exact FunctionalWeights instance`. **Status change from the final 2026-10-26 Rc10 table: none.** Factored root TX2:133 is OPEN outside Q/S. CLOSED generic field operations do not instantiate FunctionalWeights, dual-fold pair or masked terminal equations; L142/L144–L146 native/global remain.

### S10 — all source sites and continuations, including errors; artifact correspondence

Occurrences: 587 total, 219 CLOSED, 2 QUALIFIED, 366 OPEN; 242 intersect Q/S. Subject anchors: all 587 sites by definition; anchor statuses {}. Anchors inside Q/S: all slice sites for S10.

Family boundary: L166/L181 and historically L176; L187/L188; L186 accepted retirement; P7/P6 TRUST. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: L166, L181, L187, L188. Historical accepted P retirements, separately reused: L176. See the exhaustive crosswalk for candidate counts and quantifiers.

Historical support: `Low2_source_to_elf_manifest.json/Low2_final_receipt.json (accepted L186 retirement under P7); Rc10 conditional source joins`. **Status change from the final 2026-10-26 Rc10 table: none.** 366 OPEN and 2 QUALIFIED sites remain. Need complete source/error/ownership/oracle continuation coverage and coherent final dependency replay L187 plus final axioms/trust/adoption/artifact association audit L188. No new artifact correspondence/rebuild here.

## Untouched by the two slices

**No entire cone, counting its shared prerequisite footprint, is wholly outside both slices.** Every cone has shared arithmetic or source-site overlap; the JSON gives exact intersections. Claiming S8 is entirely outside is specifically false: TX1:195 and TX2:125 (`update_residue_row`) are CLOSED Q members.

**The principal subject roots of S1, S2, S3 and S9 are entirely outside both slices** under the explicitly listed anchor cuts. Their own roots receive no Q/S closure: S1 prepare/Prepared/claim, S2 native dispatcher/adapter/history, S3 pair/semantic endpoint, S9 factored Libra. For arithmetic cones the unaffected core is especially S3/S9; shared CLOSED field helpers do not close their law families. S8 accumulator construction, compact checker/expansion and final dot are outside, but residue traversal is partly inside. S10 artifact correspondence/release gates and S2 runtime association have no slice root at all. Thus “untouched since 2026-10-26” is justified for these obligations and the cone-status labels, not for every shared helper in an entire cone.

## Trust and promotion boundary

- **Added, pending owner confirmation:** RuntimeReturnData (ab), TX2:219 `emit_result`; RuntimeMemcmp (ac), TX2:226 `scan_proof_buffer`. Ledger CLOSED statuses are preserved conditionally; neither trust law is counted as discharged. Rejecting either reopens its root. Pool immediate-read/program-id/no-intervening-CPI return-data association stays OPEN.
- **Retained:** RuntimePersistence (ordinary data-byte two-transaction law, not runtime caller association); RuntimeSyscall / RuntimeSha256Value (reply value, not ordered request or experiment equality); Allocator/entrypoint/abort/rollback/library/SDK boundaries; P6/D188 option A / NativeContractSemanticTransport at exact source, feature, encoding, dictionary and tool pins. Trust reclassification is not removal of an implementation premise. P7 compiler/lowering trust remains behind historical L186 retirement.
- **D188 fidelity note:** canonical Rc9/Rc10 appendices retain rejected Parse-versus-panic divergence; both reject, but full Result equality must not be claimed. L166 still requires accepted Result/effects and both-reject/count-all-earlier-reads association. No quarantined or suspended Kani result is newly credited; no Kani verdict was produced or reclassified here.
- A promotion requires every remaining cone-era P row to be covered on its complete native/global domain by CLOSED composition or a cited accepted retirement, and exact source/artifact association. This mapping establishes no new such retirement. L154 budget and the joint non-vacuity fixture remain separate from cone counts. The security contract, constants, adversary, failure event and release target are unchanged.
