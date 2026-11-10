# NPH_ R22 final counts (CheckedVsWrapping), 2026-11-10 continuation

Job NPH_, branch codex/cx-r22-20261110, frozen target 4bb3b3f (deployed ELFs f8c0ec72…, 63ad3e9c…, built with overflow checks OFF). Sections 1, 3 and 6 are generated from NPH_R22_CONE.json by NPH_final_doc.py. **Target not yet established.**

## 1. Counts

| Judgment | Definitions | Start of this run | Change |
|---|---:|---:|---:|
| TOTAL (a) | 72 | 72 | 0 |
| DIRECT (c) | 42 | 42 | 0 |
| precondition proved from the callers (b) | 63 | 54 | +9 |
| domain lemma proved, caller join open | 0 | 0 | 0 |
| open | 20 | 29 | -9 |
| NOT_EXECUTED (excluded, ruling 1) | 28 | 28 | 0 |
| **executed (the obligation)** | **197** | 197 | +0 |
| all checked or mixed | 225 | 225 | +0 |

Rows. The executed checked or mixed definitions touch **393** CLOSED rows. **73** of them still depend on at least one open definition (153 at the start of this run). 320 are served only by TOTAL, DIRECT or (b) definitions.

Scopes this run: L087–L091 (5 of 40), every one at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, lean -j1 -M7000 -DElab.async=false, 180 s; swap 0; peak RSS ≤ 5,979,468 KiB. L087 and L088 failed on an unassigned existential witness in tail_total; L090 failed on unreduced pair projections before omega and an unfolded iterator literal; each was changed before the next scope. Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound]; no sorry. One read-only host screen (NPH_refs4_host.py on NPH_REFS5_SPEC.json, MemoryHigh 3G, MemoryMax 4G, MemorySwapMax 0, TasksMax 64). No Kani run, extraction, manifest replay, push or host deletion.

## 2. What moved in this run

Item 1 of the brief: the nine dots/accumulate/residue bodies, all to **PRECONDITION_B (b)**. They were the largest remaining exposure: 80 of the 153 exposed rows had no other open dependency.

- **Accumulator/cadence family, six bodies** (NEV_AccumulateRaw.accumulate_batched_with_node, its loop0.body, loop0_loop0.body and loop1.body; NEI_PushRaw.update_residue_row_loop0.body and loop1.body), NPH_R22Accum (L089). The cadence invariant is the closure's def predicate `S7JoinRowsTrace.Progress b.terms 0 (toBW b)`: each of the 64 residue rows carries the phase of term count t (S7Kani3PhaseInvariant.Phase), which bounds each cell between flushes; push (one per row per accumulate call, the term count unchanged by push) and the flush on terms % 4 = 3 preserve it inside NBF_RowsTotal (NBF_Progress.body). With the numeric fields of NFS_NEV_AccumPacket.Domain (width 64, raw length 64, a.next < 22, b.terms < 22, canonical value, rhs, power and rho) it gives `acc_total`: the **whole checked accumulate is ok for every node**. The proof composes NFS_NEV_BasisProducer.total (basis loops ok and canonical for every node), NBF_RowsTotal.full and NFS_NEV_RowLoop.association (raw row loop = model row loop, no success premise) into `rows_total`, and `tail_total` (terms + 1, a.next + 1, the three field callees). The state producers are the closure's: the pending constructor gives Progress 0 0 (NBF_FirstRows.constructor_progress), and NFS_QueryInvariant.Domain carries the predicate at every reached query state (NFS_QueryInvariant.step; NPH_R22JoinCW2.reach_domain on tx2, NFS_PacketRoot.Domain.invariant on tx1). `acc_site` and `installed_ok` compose it at the call: inside the loop guard (a.next < finish ≤ 22) with the canonical line value (NFS_AccumDomain.line), the installed accumulate of NFS_QueryOps.installed equals NFS_AccumInstall.run and is ok. Since the enclosing call is ok, every execution of the five inner bodies inside it is ok. So every checked operation in them succeeds, and the wrapping reading equals the checked result.
- **Dots family, three bodies** (FIp_NativeDots four_dots_one, four_dots_one_loop0.body, four_dots_one_loop0_loop0.body), NPH_R22Dots (L091). Two def predicates on the loop states are used. `InnerInv` says the term window has at most 4 terms ending at or before 26, and every u64 sum is at most (terms so far)·(P−1)². `OuterInv` says that after k ≤ 7 windows the StepBy iterator is at min(4k, 26), with every limb at most k·R. Each is entered by its caller (inner_entry, outer_entry) and preserved by every successful step (inner_step, outer_step). On them:
  - every checked operation is ok: slot_ops, outer_ops, update_ok, read_arith;
  - the inner body is ok whenever the scalar read succeeds (inner_ok). read_arith shows that the read's remaining steps are non-arithmetic: range index, try_from, unwraps, decode.
  The caller domain is slot < 4 and canonical g. The slots are the literals 0..3 of four_dots (adapter_calls). Canonical g comes from NFS_PacketRoot.Domain.gCanonical on tx1 (tx1_g) and from NFW_PowersDomain.query_domain on tx2. Unlike the accumulate family, a decode failure can make these bodies abort, but only at a non-arithmetic step that aborts in both profiles. That reading is listed in section 4.
- Caller structure for all nine comes from a new backward screen, NPH_REFS5.json (section 4).

Not changed: no ops interface, merged module, closed-row statement, field premise, trust row or contract. Every moved definition records its previous judgment under `nph_judgment_before_item1acc` or `nph_judgment_before_item1dots`, and its theorems under `nph_theorems`.

## 3. Definitions still open (20), largest row fan-out first

"Only blocker" counts the rows for which this definition is the single remaining open dependency.

| Rows | Only blocker | Definition | Pattern class | What closes it |
|---:|---:|---|---|---|
| 37 | 9 | `AspisR1WeightsFieldCurrent.weights.field` | INDEX_ARITHMETIC_ON_CALLER_DOMAIN | i*32, i+1, (i+1)*32 before the range read: a multiplication can wrap onto a valid range, so this is not fail/fail; needs i < len/32 from the finishField callers (CurrentWide.Proof.finishField loop indices). |
| 31 | 1 | `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | value*32 and byte_offset + i, start + 1..31 point reads: the point-read chain (NPH_R22Loops5.point_step) covers start+k after the first read; value*32 and byte_offset + value*32 need value < 29 and the record offset bound from decode_k_loop. |
| 28 | 1 | `MultiproofConeRef.reference.write_parent` | LOOP_INVARIANT | index / 2 is ok for every input; w + 1 needs w < 16 (Scratch row width) from level_rows/binary_step. |
| 27 | 4 | `AspisR72Sampler.field.r24_canonical_mul` | NO_FROZEN_COUNTERPART | provenance first (no frozen source). R22-wise its checked ops are the Q.raw shape (u64 products of widened u32 limbs, 2*u, 2*v, 3*P), so the NPH_R22QRawTotal argument should apply once the body is pinned; not proved. |
| 24 | 0 | `MultiproofConeRef.reference.leaf_step` | LOOP_INVARIANT | s.n - 1 is guarded by s.n > 0 (DIRECT pattern); s.n + 1 needs s.n < 16 (Scratch capacity) along the leaf fold. |
| 23 | 0 | `AspisR1PrefixAggregateParser.r1_wire.parse_record` | PRODUCER_BOUND | 5 + size with size from row_shape (ok (table row), sizes <= 3712 by the ExtractedRowShape table): one table-bound lemma closes it. |
| 23 | 0 | `AspisR1PrefixAggregateParser.r1_wire.parse_record_at` | PRODUCER_BOUND + CURSOR_ADD_THEN_RANGE_GET | 5 + size as above; offset + length is followed by Slice.get [offset, offset+length) whose none result becomes Err(Length): needs a Slice.get success lemma (the analogue of T2Nat_RawBounds.range_success) to give Err/Err agreement. |
| 21 | 6 | `OraclePortCkptAbi2Extracted.body_byte` | GUARDED_SUBTRACTION_CHAIN | i - c under the body range guards (i >= c on each branch), / 32 and % 32 by constants: expected DIRECT by per-branch guard reading; not yet written. |
| 18 | 0 | `AspisR1Post25Sampler.sampler.low_base_p_digits_loop0.body` | LOOP_INVARIANT | 4*i, start + 1..3 and i + 1 with i < 8: guarded index arithmetic once the loop guard i < 8 is read (DIRECT pattern expected). |
| 18 | 0 | `AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body` | LOOP_INVARIANT | j - 1 (needs j > 0 guard), remainder <<< 32 (ok), dividend / P and % P (nonzero constant): DIRECT expected once the j guard is read; remainder < P invariant for the shift-or. |
| 17 | 1 | `AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body` | LOOP_INVARIANT | sum = digit + carry needs digit < P and carry small (base-P digit invariant); % and / by the nonzero base; i + 1 guarded. |
| 16 | 0 | `AspisR1GammaCaller.sampler.gamma_sample` | PRODUCER_BOUND | quotient + 1 (u32): needs quotient < 2^32 - 1 from the ops.low producer (the sampler low digits). |
| 14 | 0 | `MultiproofConeRef.reference.binary_step` | LOOP_INVARIANT | i + 1, i + 2, i4 - s.at, s.at + 32: needs i < s.n <= 16 and s.at <= i from the level loop. |
| 9 | 0 | `NCV_Reference.bytes32_loop.body` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | s + i with i < 32 before a point read: needs s + 32 <= len from the callers (decode_* readers). |
| 9 | 0 | `NCV_Reference.decode_frontier_loop.body` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | 32*level, 48 + .., next >>> level, level + 1: needs level < 64 (frontier depth) from the loop guard. |
| 9 | 0 | `NCV_Reference.digest_loop.body` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | 4*i, s + 4i with i < 8: needs s + 32 <= len from the callers. |
| 7 | 0 | `AspisS1NativeCompact.compact.expand_semantic_loop.body` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | dst + 5, src + 5, size/2, src + size: needs the compact-record length bound (sizes from row_shape <= 3712, src/dst within the 57607-byte proof). |
| 7 | 0 | `AspisS1ValuesOwned.copy_chunk_loop.body` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | chunk*16 + byte, chunk*32 + 16 + byte with byte < 16: needs chunk < count (values loop guard) and count <= len/32. |
| 7 | 0 | `AspisS1ValuesOwned.values_owned_reference` | CURSOR_ARITHMETIC_ON_CALLER_DOMAIN | i % 16 (ok), 2*i3, i5 / 16 (ok): 2*i3 needs i3 <= len bound from the caller expandValues. |
| 4 | 0 | `AspisR1CurrentCaller.verifier.candidate.prepare` | PRODUCER_BOUND | one checked i + i1 (compact offsets): needs the offset producers (CurrentCompact layout constants, NPH_R22JoinCW6 ls_eq/os_eq) composed at this add. |

By class: CURSOR_ARITHMETIC_ON_CALLER_DOMAIN 7; LOOP_INVARIANT 6; PRODUCER_BOUND 3; INDEX_ARITHMETIC_ON_CALLER_DOMAIN 1; NO_FROZEN_COUNTERPART 1; PRODUCER_BOUND + CURSOR_ADD_THEN_RANGE_GET 1; GUARDED_SUBTRACTION_CHAIN 1.

Exposure structure: 22 rows depend on exactly one open definition.

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
| Checked-operation enumeration of each DIRECT/TOTAL-by-pattern body (NPH_LOOPS_SCREEN.json, the census body screen, and the host source reading NPH_hostops.py/NPH_hostbody.py of this run) | that the listed operations are the body's only overflow-checked bindings (everything else is indexing, update, comparison, pure bit operation, explicit wrapping_* or a callee with its own judgment). The Lean lemma proves each listed operation safe; the completeness of the list is read from the gate text. | every DIRECT judgment (42), the bodies whose TOTAL judgment cites a per-operation lemma, and, this run, the dots inner body: NPH_R22Dots.read_arith proves in Lean that after the safe read arithmetic the read is only the range index, try_from, two unwraps and the decode; that these abort in both profiles (bounds checks and panics on in both) is read from the gate text |

Separate from the screens, and unchanged: the reading of the operational tree as the compiled code is the P6/P7 interpretation (Aeneas translation fidelity and the compiler trust lines of NOX_REALIZATION.md); Lean does not load the ELF. The NOT_EXECUTED exclusions apply lead ruling 1 to new cases by principle; the lead may reverse any of them, in which case that body returns to OPEN with its recorded previous judgment.

## 5. Proposed wording for the claim document (section 4.3, CheckedVsWrapping row)

> **CheckedVsWrapping (R22, OPEN).** The gate's emitted bodies for the reached definitions are checked translations (an overflow is an error result); the deployed ELFs (f8c0ec72…, 63ad3e9c…, built from 4bb3b3f) wrap. The theorem transfers to the deployed binary when, for every executed checked or mixed definition, the checked body is total on every input (TOTAL), or total on a domain that its reached callers are proved to supply (b), or wrapping acceptance is proved to imply checked acceptance directly (DIRECT); R22TotalCheckedComposition then gives safety of every executed checked operation and equality of the wrapping and checked results, under the P6/P7 interpretation of the operational tree as the compiled code. Status at 4bb3b3f (NPH_, evidence/r22-final-20261110/NPH_R22_FINAL_COUNTS.md): of 225 checked or mixed definitions, 28 are proof-only references excluded under lead ruling 1 on textual referrer screens; of the 197 executed, 72 are TOTAL, 42 DIRECT, 63 (b) and 20 open. 73 of the 393 CLOSED rows these definitions serve depend on an open definition. No reachable input on which the wrapping binary accepts and the checked model rejects is known. Residual: the 20 open definitions of NPH_R22_FINAL_COUNTS.md section 3 (7 cursor bounds owed by their callers, 6 loop invariants, 4 producer bounds, 1 index-arithmetic caller domain, 1 guarded subtraction chain, 1 body without a frozen counterpart). Removal condition: every executed definition in (a), (b) or (c) on the final replayed closure, with each textual screen of section 4 replaced by a Lean statement or accepted by the owner as a named review item; otherwise the owner records R22 as a retained trust row, named in the claim's first sentence.

The 2021 figures (35 TOTAL / 63 ACCEPTED-ONLY / 48 OTHER of 146 statements) concern a different object and remain superseded for this row.

## 6. Appendix: row IDs of the open definitions

- `AspisR1WeightsFieldCurrent.weights.field` (37): TX1:087, TX1:094, TX1:158, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:193, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:064, TX2:065, TX2:114, TX2:115, TX2:116, TX2:119, TX2:129, TX2:135, TX2:137, TX2:141, TX2:142, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225, TX2:240, TX2:241
- `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value` (31): TX1:087, TX1:094, TX1:098, TX1:129, TX1:133, TX1:134, TX1:136, TX1:137, TX1:147, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:193, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225
- `MultiproofConeRef.reference.write_parent` (28): TX1:081, TX1:082, TX1:083, TX1:084, TX1:087, TX1:094, TX1:127, TX1:136, TX1:137, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:053, TX2:054, TX2:055, TX2:064, TX2:065, TX2:093, TX2:213, TX2:221, TX2:240, TX2:241
- `AspisR72Sampler.field.r24_canonical_mul` (27): TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225
- `MultiproofConeRef.reference.leaf_step` (24): TX1:081, TX1:082, TX1:083, TX1:087, TX1:094, TX1:136, TX1:137, TX1:168, TX1:169, TX1:170, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:053, TX2:054, TX2:055, TX2:064, TX2:065, TX2:213, TX2:221, TX2:240, TX2:241
- `AspisR1PrefixAggregateParser.r1_wire.parse_record` (23): TX1:087, TX1:094, TX1:098, TX1:129, TX1:133, TX1:134, TX1:136, TX1:137, TX1:138, TX1:142, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `AspisR1PrefixAggregateParser.r1_wire.parse_record_at` (23): TX1:087, TX1:094, TX1:098, TX1:129, TX1:133, TX1:134, TX1:136, TX1:137, TX1:138, TX1:142, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `OraclePortCkptAbi2Extracted.body_byte` (21): TX1:064, TX1:087, TX1:094, TX1:136, TX1:137, TX1:168, TX1:169, TX1:170, TX1:174, TX1:175, TX1:178, TX1:186, TX1:327, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:210, TX2:213, TX2:221
- `AspisR1Post25Sampler.sampler.low_base_p_digits_loop0.body` (18): TX1:087, TX1:094, TX1:157, TX1:158, TX1:159, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body` (18): TX1:087, TX1:094, TX1:157, TX1:158, TX1:159, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body` (17): TX1:087, TX1:094, TX1:155, TX1:158, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `AspisR1GammaCaller.sampler.gamma_sample` (16): TX1:087, TX1:094, TX1:158, TX1:160, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221
- `MultiproofConeRef.reference.binary_step` (14): TX1:081, TX1:082, TX1:083, TX1:127, TX1:168, TX1:169, TX1:170, TX1:186, TX2:053, TX2:054, TX2:055, TX2:064, TX2:065, TX2:093
- `NCV_Reference.bytes32_loop.body` (9): TX1:330, TX1:333, TX2:213, TX2:217, TX2:221, TX2:233, TX2:240, TX2:241, TX2:242
- `NCV_Reference.decode_frontier_loop.body` (9): TX1:330, TX1:333, TX2:213, TX2:217, TX2:221, TX2:233, TX2:240, TX2:241, TX2:242
- `NCV_Reference.digest_loop.body` (9): TX1:330, TX1:333, TX2:213, TX2:217, TX2:221, TX2:233, TX2:240, TX2:241, TX2:242
- `AspisS1NativeCompact.compact.expand_semantic_loop.body` (7): TX1:098, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186
- `AspisS1ValuesOwned.copy_chunk_loop.body` (7): TX1:098, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186
- `AspisS1ValuesOwned.values_owned_reference` (7): TX1:098, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:186
- `AspisR1CurrentCaller.verifier.candidate.prepare` (4): TX1:168, TX1:169, TX1:170, TX1:186

Target not yet established.
