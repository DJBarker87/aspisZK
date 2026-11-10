# NPH_ R22 final counts (CheckedVsWrapping), 2026-11-10 continuation

Job NPH_, branch codex/cx-r22-20261110, frozen target 4bb3b3f (deployed ELFs f8c0ec72…, 63ad3e9c…, built with overflow checks OFF). Sections 1, 3 and 6 are generated from NPH_R22_CONE.json by NPH_final_doc.py. **Target not yet established.**

## 1. Counts

| Judgment | Definitions | Start of this run | Change |
|---|---:|---:|---:|
| TOTAL (a) | 72 | 72 | 0 |
| DIRECT (c) | 52 | 42 | +10 |
| precondition proved from the callers (b) | 68 | 54 | +14 |
| domain lemma proved, caller join open | 0 | 0 | 0 |
| open | 5 | 29 | -24 |
| NOT_EXECUTED (excluded, ruling 1) | 28 | 28 | 0 |
| **executed (the obligation)** | **197** | 197 | +0 |
| all checked or mixed | 225 | 225 | +0 |

Rows. The executed checked or mixed definitions touch **393** CLOSED rows. **55** of them still depend on at least one open definition (153 at the start of this run). 338 are served only by TOTAL, DIRECT or (b) definitions.

Scopes this run: L087–L096 (10 of 40), every one at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, lean -j1 -M7000 -DElab.async=false, 180 s; swap 0; peak RSS ≤ 5,979,468 KiB. Five failed on proof-script details and each was changed before the next scope: L087 and L088 (an unassigned existential witness in tail_total), L090 (unreduced pair projections before omega, an unfolded iterator literal), L092 (a conjunct shape of frontier_ops/cc_ops) and L094 (two bound proofs). Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound]; no sorry. Two read-only host screens (NPH_refs4_host.py on NPH_REFS5_SPEC.json and NPH_REFS6_SPEC.json, MemoryHigh 3G, MemoryMax 4G, MemorySwapMax 0, TasksMax 64). No Kani run, extraction, manifest replay, push or host deletion.

## 2. What moved in this run

Twenty-four definitions moved: 15 to (b) and 9 to DIRECT. Open went from 29 to 5. Rows exposed went from 153 to 55.

**Item 1: the nine dots/accumulate/residue bodies, all to PRECONDITION_B (b).** They were the largest remaining exposure: 80 of the 153 exposed rows had no other open dependency.

- **Accumulator/cadence family, six bodies** (NEV_AccumulateRaw.accumulate_batched_with_node, its loop0.body, loop0_loop0.body and loop1.body; NEI_PushRaw.update_residue_row_loop0.body and loop1.body), NPH_R22Accum (L089). The cadence invariant is the closure's def predicate `S7JoinRowsTrace.Progress b.terms 0 (toBW b)`: each of the 64 residue rows carries the phase of term count t (S7Kani3PhaseInvariant.Phase), which bounds each cell between flushes; push (one per row per accumulate call, the term count unchanged by push) and the flush on terms % 4 = 3 preserve it inside NBF_RowsTotal (NBF_Progress.body). With the numeric fields of NFS_NEV_AccumPacket.Domain (width 64, raw length 64, a.next < 22, b.terms < 22, canonical value, rhs, power and rho) it gives `acc_total`: the **whole checked accumulate is ok for every node**. The proof composes NFS_NEV_BasisProducer.total (basis loops ok and canonical for every node), NBF_RowsTotal.full and NFS_NEV_RowLoop.association (raw row loop = model row loop, no success premise) into `rows_total`, and `tail_total` (terms + 1, a.next + 1, the three field callees). The state producers are the closure's: the pending constructor gives Progress 0 0 (NBF_FirstRows.constructor_progress), and NFS_QueryInvariant.Domain carries the predicate at every reached query state (NFS_QueryInvariant.step; NPH_R22JoinCW2.reach_domain on tx2, NFS_PacketRoot.Domain.invariant on tx1). `acc_site` and `installed_ok` compose it at the call: inside the loop guard (a.next < finish ≤ 22) with the canonical line value (NFS_AccumDomain.line), the installed accumulate of NFS_QueryOps.installed equals NFS_AccumInstall.run and is ok. Since the enclosing call is ok, every execution of the five inner bodies inside it is ok. So every checked operation in them succeeds, and the wrapping reading equals the checked result.
- **Dots family, three bodies** (FIp_NativeDots four_dots_one, four_dots_one_loop0.body, four_dots_one_loop0_loop0.body), NPH_R22Dots (L091). Two def predicates on the loop states are used. `InnerInv` says the term window has at most 4 terms ending at or before 26, and every u64 sum is at most (terms so far)·(P−1)². `OuterInv` says that after k ≤ 7 windows the StepBy iterator is at min(4k, 26), with every limb at most k·R. Each is entered by its caller (inner_entry, outer_entry) and preserved by every successful step (inner_step, outer_step). On them:
  - every checked operation is ok: slot_ops, outer_ops, update_ok, read_arith;
  - the inner body is ok whenever the scalar read succeeds (inner_ok). read_arith shows that the read's remaining steps are non-arithmetic: range index, try_from, unwraps, decode.
  The caller domain is slot < 4 and canonical g. The slots are the literals 0..3 of four_dots (adapter_calls). Canonical g comes from NFS_PacketRoot.Domain.gCanonical on tx1 (tx1_g) and from NFW_PowersDomain.query_domain on tx2. Unlike the accumulate family, a decode failure can make these bodies abort, but only at a non-arithmetic step that aborts in both profiles. That reading is listed in section 4.
- Caller structure for all nine comes from a new backward screen, NPH_REFS5.json (section 4).

**Item 2: cursor and index bodies, NPH_R22Cursor (L093).**
- NCV bytes32_loop.body and digest_loop.body move to (b) on reached-cursor loop invariants. BInv says i = 0 or s + i ≤ len. DInv says i = 0 or s + 4i ≤ len, using word32_bound: a successful word32 at t gives t + 4 ≤ len. Each invariant is entered at 0 by the only caller and kept by every cont step. These bodies needed **no caller length bound**, because the point-read chain itself bounds the cursor.
- decode_frontier_loop.body moves to DIRECT: the guard is level < 20, not 64.
- AspisS1NativeCompact expand_semantic_loop.body moves to DIRECT. Every cursor add is followed by a bounds-checked range read (NPH_R22Loops4.cursor_direct) or a range index_mut (new mut_cursor_direct, range_mut_success).
- decode_k_value moves to (b) on DK. The domain is established by the enclosing decode_k: its own checked_mul/checked_add guards returned Some (dk_guards, via the new checked_mul_some/checked_add_some converses), and the loop iterator keeps end = N (dk_value, dk_step).
- copy_chunk_loop.body moves to (b) on chunk·32 + 31 ≤ usize max. That bound follows from values_owned_reference's checked 2·len and count = len / 16 (vo_guards, cc_domain) and the guard chunk < count.
- values_owned_reference and weights.field stay open. Their producers are located and recorded in section 3.

**Item 3: loop, producer and subtraction bodies, NPH_R22Direct (L095) and NPH_R22Gamma (L096).**
- parse_record moves to DIRECT: every row_shape size is ≤ 3712 (table_size on ExtractedRowShape.table).
- parse_record_at moves to DIRECT, the same table bound plus get_cursor_direct. A reading is **flagged**: when the wrapped get returns None, the wrapping program returns Err(Length) where the checked model aborts. Both are rejections because Prefix.parse propagates the Err with ?.
- OraclePortCkptAbi2Extracted body_byte moves to DIRECT: guarded_sub on every else branch, divrem_ok for the constant divisors, and the e_byte pattern.
- The three sampler loop bodies move to DIRECT:
  - qm31_div_pass_loop.body: j − 1 under j > 0, the u64 shift by 32, and / and % by P;
  - low_base_p_digits_loop0.body: guarded index arithmetic;
  - add_small_base_p_loop.body: a u64 sum of two u32 cannot overflow.
  No digit or remainder invariant was needed, contrary to the earlier notes.
- MultiproofConeRef write_parent and leaf_step move to DIRECT: the increment follows a successful Array.update on a 16-entry array (update_lt). leaf_step's decrement is guarded.
- AspisR1GammaCaller gamma_sample moves to (b). The quotient is rank / P^8 ≤ 256 on low_base_p_digits, and both closure helper records install that low. This caller reading is flagged.
- binary_step stays open. A wrapped len(nodes) − s.at can reach the accepting Stop branch, so it needs the traversal invariant s.at ≤ len(nodes).
- prepare stays open: it needs the installed op15 value.
- r24_canonical_mul stays as recorded (item 4).

Not changed: no ops interface, merged module, closed-row statement, field premise, trust row or contract. Every moved definition records its previous judgment under `nph_judgment_before_item1acc`, `_item1dots`, `_item2` or `_item3`, and its theorems under `nph_theorems`.

## 3. Definitions still open (5), largest row fan-out first

"Only blocker" counts the rows for which this definition is the single remaining open dependency.

| Rows | Only blocker | Definition | Pattern class | What closes it |
|---:|---:|---|---|---|
| 37 | 15 | `AspisR1WeightsFieldCurrent.weights.field` | INDEX_ARITHMETIC_ON_CALLER_DOMAIN | i*32, i+1, (i+1)*32 before the range read: a wrapped window can be valid, so this is not fail/fail. Domain lemma exists in the closure: NJU_FieldScalar.checked (all three ops ok for i < 64). Located callers (via AspisR1CurrentWide.Proof.finishField, NPH_REFS6.json): finish_relation_round reads the literals 0 and 4; finish_query_dot_loop.body reads j < len weights; the polynomial and AspisR1CurrentPreparedClaim.ClaimParser.field indices. Needs len weights <= 64 at the reached finish dot (and the polynomial/claim-parser index bounds) composed at the deployed finish (NPH_R22JoinCW2.tx2_finish_round context). |
| 27 | 7 | `AspisR72Sampler.field.r24_canonical_mul` | NO_FROZEN_COUNTERPART | provenance first (no frozen source). R22-wise its checked ops are the Q.raw shape (u64 products of widened u32 limbs, 2*u, 2*v, 3*P), so the NPH_R22QRawTotal argument should apply once the body is pinned; not proved. |
| 14 | 8 | `MultiproofConeRef.reference.binary_step` | LOOP_INVARIANT | i + 1 follows a bounds-checked read s.idx[i] (16 entries) and i + 2 runs after a read at i + 1, so both are DIRECT by NPH_R22Direct.update_lt-style reads; but len(nodes) - s.at has no guard, and if s.at > len the wrapped difference can be < 32 so the wrapping program takes the Stop branch (accepting path) where the checked model aborts. Needs the traversal invariant s.at <= len(nodes) (s.at starts at 0 and only advances to s.at + 32 after a successful read of nodes[s.at, s.at + 32)) composed over the level loop. |
| 7 | 3 | `AspisS1ValuesOwned.values_owned_reference` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | i % 16 and i5 / 16 are ok for every input; 2 * len(input) needs len(input) <= usize max / 2 at the call. Located producer (not composed): the only executing caller AspisS1ValuesOwnedInstallation.expandValues is the expandValues callback of expand_semantic_loop.body, called on s3 = input[i1, i1 + size/2) with size <= 3712 (NPH_R22Direct.prefix_shape_size pattern on the compact row_shape), so len(s3) <= 1856; needs the range-index length lemma (NGV_ByteWindow.read/select_length) and the installed-ops tie. |
| 4 | 0 | `AspisR1CurrentCaller.verifier.candidate.prepare` | PRODUCER_BOUND | one checked i + i1 with i = compact.LOGICAL_SEMANTIC ops = ops.op15 (an irreducible callback constant) and i1 = compact.LOGICAL_Y1 = 29*32 = 928: needs the value of op15 in the installed prepare record at the reached caller (CurrentCompact layout; NPH_R22JoinCW6 ls_eq/os_eq show the slot is unchanged by op8 replacement), then one add_ok. |

By class: INDEX_ARITHMETIC_ON_CALLER_DOMAIN 1; NO_FROZEN_COUNTERPART 1; LOOP_INVARIANT 1; CURSOR_ARITHMETIC_ON_CALLER_DOMAIN 1; PRODUCER_BOUND 1.

Exposure structure: 33 rows depend on exactly one open definition.

## 4. Every textual-screen reliance (one place)

None of these is a Lean statement. Each is flagged for lead review; a release claim must either replace it with a Lean statement or record it as an accepted review item.

| Screen | What it decides | Where it is relied on |
|---|---|---|
| NPH_SITES.json (NPH_sites_scan2.py / NPH_sites_status.py) | the site checklist of every field family (CW, SM, QA, SC, R72, FIq): which reached bodies call a domain-only kernel. Cannot see calls through notation, instance resolution or callback records beyond those traced. | sections 13–19; every (b) move of the six field families |
| Call-pattern reading of Port3_NativeQueryBody / Port3_NativeGeometryBody | which QA callbacks the executed query and geometry bodies invoke, the executed dictionaries Dcon/Dsel and the geometry stage path | QA (b), section 18 |
| op9 → prepare → tx1 → op10 → first_decoded → stage1_owned call chain | that every op9 (and so every finish/terminal) execution of the 345 entry is inside the guarded installation | SM (b) and FIq (b), sections 18a, 19b |
| NPH_FIQ_REFS.json (backward screen, NPH_fiq_refs_host.py) | 114 FIq sites PROOF_ONLY → NOT_EXECUTING; 33 FIq definitions COVERED_BY_TERMINAL → (b); the NNG 136 model callers (c7 slot) tied only by theorems | FIq (b), section 19c–d |
| NPH_SUM3_REFS.json and the SC proof-only referrers | SM-copy sum3 site NOT_EXECUTING; SC non-deployed referrers proof-only | SM (b), SC (b), sections 17–18 |
| NPH_R6X_REFERRERS.json | the five R65/R66 kernels are proof-only references (ruling 1 → NOT_EXECUTED) | denominator 225 → 220, section 13 |
| NPH_REFS4_A.json (backward screen, NPH_refs4_host.py, this run) | 23 bodies PROOF_ONLY → NOT_EXECUTED; the caller structure of the TerminalDecoder digest encode loop (its only executing chain is encode_digest_canonical_loop ← encode_digest_canonical). Positive controls NBO_FieldSemantics.add, FIp_SemanticArithmetic.mask, NFS_QueryOps.installed, NBF_BasisInstall.install all classify as executing. | denominator 220 → 197; encode loop (b), this run |
| NPH_REFS5.json (backward screen, NPH_refs4_host.py with NPH_REFS5_SPEC.json, this run) | the caller structure of the item-1 family: every upward path from the six accumulate/residue bodies meets NEV accumulate or NFS_AccumInstall.run, and every upward path from the three dots bodies meets FIp_DotsAdapter.dots (through four_dots); the remaining tops (NFS_NEV_AccumulateTail.rows, NFS_NEV_BasisProducer.source, NEI_FourWrapper.four_dots, the JFs_/NFE_ step models) are theorem-only with no tie candidate. Same positive controls as NPH_REFS4_A.json. | the nine item-1 (b) moves, this run (section 2) |
| NPH_REFS6.json (backward screen, NPH_refs4_host.py with NPH_REFS6_SPEC.json, this run) | the direct definition referrers of the item-2 targets: decode_k_value only from decode_k_loop.body (plus the theorem-side readback AspisR1DecodeKFullLoopReadback.decodedAt), decode_k from the two decodeMain adapters, copy_chunk_loop.body only from copy_chunk_loop, values_owned_reference only from AspisS1ValuesOwnedInstallation.expandValues, weights.field only from AspisR1CurrentWide.Proof.finishField, and the NCV/compact loop bodies only from their own loops | the item-2 (b) moves (decode_k_value, copy_chunk_loop.body, bytes32/digest loops), this run |
| parse_record_at Err/abort reading (gate text of r1_wire.Prefix.parse) | that on the wrapped-end path the wrapping program's Err(Length) and the checked model's abort are both rejections, because every parse_record_at result passes through ? in Prefix.parse | parse_record_at DIRECT, this run |
| GammaHelpers record at the executed gamma_sample (closure reading, no screen) | that the executed gamma_sample runs on candidateHelpers or candidateGammaHelpers, both of which install low = low_base_p_digits (helpers_low is a Lean statement about the two records, not about which one executes) | gamma_sample (b), this run |
| Checked-operation enumeration of each DIRECT/TOTAL-by-pattern body (NPH_LOOPS_SCREEN.json, the census body screen, and the host source reading NPH_hostops.py/NPH_hostbody.py of this run) | that the listed operations are the body's only overflow-checked bindings (everything else is indexing, update, comparison, pure bit operation, explicit wrapping_* or a callee with its own judgment). The Lean lemma proves each listed operation safe; the completeness of the list is read from the gate text. | every DIRECT judgment (42), the bodies whose TOTAL judgment cites a per-operation lemma, and, this run, the dots inner body: NPH_R22Dots.read_arith proves in Lean that after the safe read arithmetic the read is only the range index, try_from, two unwraps and the decode; that these abort in both profiles (bounds checks and panics on in both) is read from the gate text |

Separate from the screens, and unchanged: the reading of the operational tree as the compiled code is the P6/P7 interpretation (Aeneas translation fidelity and the compiler trust lines of NOX_REALIZATION.md); Lean does not load the ELF. The NOT_EXECUTED exclusions apply lead ruling 1 to new cases by principle; the lead may reverse any of them, in which case that body returns to OPEN with its recorded previous judgment.

## 5. Proposed wording for the claim document (section 4.3, CheckedVsWrapping row)

> **CheckedVsWrapping (R22, OPEN).** The gate's emitted bodies for the reached definitions are checked translations (an overflow is an error result); the deployed ELFs (f8c0ec72…, 63ad3e9c…, built from 4bb3b3f) wrap. The theorem transfers to the deployed binary when, for every executed checked or mixed definition, the checked body is total on every input (TOTAL), or total on a domain that its reached callers are proved to supply (b), or wrapping acceptance is proved to imply checked acceptance directly (DIRECT); R22TotalCheckedComposition then gives safety of every executed checked operation and equality of the wrapping and checked results, under the P6/P7 interpretation of the operational tree as the compiled code. Status at 4bb3b3f (NPH_, evidence/r22-final-20261110/NPH_R22_FINAL_COUNTS.md): of 225 checked or mixed definitions, 28 are proof-only references excluded under lead ruling 1 on textual referrer screens; of the 197 executed, 72 are TOTAL, 52 DIRECT, 68 (b) and 5 open. 55 of the 393 CLOSED rows these definitions serve depend on an open definition. No reachable input on which the wrapping binary accepts and the checked model rejects is known. Residual: the 5 open definitions of NPH_R22_FINAL_COUNTS.md section 3. These are weights.field's caller index domain, binary_step's traversal invariant s.at ≤ len(nodes), values_owned_reference's caller length, prepare's installed op15 constant, and r24_canonical_mul, which has no frozen counterpart. Removal condition: every executed definition in (a), (b) or (c) on the final replayed closure, with each textual screen of section 4 replaced by a Lean statement or accepted by the owner as a named review item; otherwise the owner records R22 as a retained trust row, named in the claim's first sentence.

The 2021 figures (35 TOTAL / 63 ACCEPTED-ONLY / 48 OTHER of 146 statements) concern a different object and remain superseded for this row.

## 6. Appendix: row IDs of the open definitions

- `AspisR1WeightsFieldCurrent.weights.field` (37): TX1:087, TX1:094, TX1:158, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:193, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:064, TX2:065, TX2:114, TX2:115, TX2:116, TX2:119, TX2:129, TX2:135, TX2:137, TX2:141, TX2:142, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225, TX2:240, TX2:241
- `AspisR72Sampler.field.r24_canonical_mul` (27): TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225
- `MultiproofConeRef.reference.binary_step` (14): TX1:081, TX1:082, TX1:083, TX1:127, TX1:168, TX1:169, TX1:170, TX1:186, TX2:053, TX2:054, TX2:055, TX2:064, TX2:065, TX2:093
- `AspisS1ValuesOwned.values_owned_reference` (7): TX1:098, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186
- `AspisR1CurrentCaller.verifier.candidate.prepare` (4): TX1:168, TX1:169, TX1:170, TX1:186

Target not yet established.
