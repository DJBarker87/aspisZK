<<resources>>
Scopes this run: L097–L103 (7 of 30), one at a time, every one at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, lean -j1 -M7000 -DElab.async=false, 180 s; swap 0; peak RSS ≤ 6,809,376 KiB; from L098 on each launch also checked `free -g` available ≥ 12 GB (lead instruction). Three failed, all on NPH_R22ValuesSite, and each was changed before the next scope: L099 (anonymous-constructor placeholders for the offset witnesses), L100 (rfl cannot assign an offset metavariable through the checked add; the constants were then stated), L101 (an unclosed numeral goal; omega added). Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound]; no sorry. One read-only host screen (NPH_refs4_host.py on NPH_REFS7_SPEC.json, MemoryHigh 3G, MemoryMax 4G, MemorySwapMax 0, TasksMax 64). No Kani run, extraction, manifest replay, push or host deletion. The previous run (L087–L096) is recorded in NPH_R22_STATUS.md section 21.

<<moved>>
Four definitions moved: three to (b) and one from OPEN to domain-lemma-proved. Open went from 5 to 1, plus 1 domain-only. Rows exposed went from 55 to 44.

**Item 1: binary_step to (b), NPH_R22Binary (L097).** This was the one site where a wrapping-accepts/checked-rejects mismatch could have occurred. No such input exists: the traversal invariant holds on every reached state.
- `AtInv nodes s` is the def predicate s.at ≤ len nodes.
- `Reached` is the set of traversal states. It starts at the levels entry {s with at := 0} of verify_owned and Port9OR_P6Verify.factored. It is closed under the Next step of binary_step (the level_rows recursion) and under the Done result of level_rows (the levels recursion).
- `step_next`: every successful Next step keeps AtInv, keeps n and advances i. The new cursor is either s.at (the paired-sibling arm) or s.at + 32, after the range read nodes[s.at, s.at + 32) succeeded.
- `rows_done`: a Done result of level_rows from an AtInv state is an AtInv state, by induction on n − i.
- `reached_inv` and `reached_ops`: at every reached state every checked operation of binary_step that executes is ok with the mathematical value. These are i + 1 and i + 2 after bounds-checked reads on the 16-entry index array, len(nodes) − s.at (exact, so the wrapping difference is the same value and the Stop test takes the same branch), and s.at + 32 off the Stop branch.
- No hash totality and no node-length premise is used.
- **Correction:** the earlier open note called the Stop branch an accepting path. It is a rejection: levels returns Stop and verify_owned returns false.
- The call structure comes from the gate text and the new backward screen NPH_REFS7.json (section 4).

**Item 3: values_owned_reference to (b), NPH_R22Values (L098) and NPH_R22ValuesSite (L102).**
- Its 2·len is ok for len ≤ 1856 (vo_mul_ok). Its % 16 and / 16 are ok for every input.
- Both executing call sites of expandValues supply that length:
  - the compact expand site passes input[i1, i1 + size/2) with size ≤ 3712 from the compact row_shape (compact_site);
  - candidate.prepare's op11 is expandValues at every installed configuration (installed_op11), and its argument is the Y1 window proof[7031, 7495), width 464 (installed_slots: op12 = 16, op13 = 7015, op14 = 464; installed_window, installed_y1_site).

**Item 4: prepare to (b), NPH_R22Values (L098).** At every installed configuration op15 is the constant 13831 (installed_ls, rfl for every cfg). The op8 replacement of NPH_R22JoinCW6 leaves it unchanged (guarded_ls). LOGICAL_Y1 is 928, and 13831 + 928 = 14759 is ok (prepare_add), so prepare's only checked operation is ok on every input.

**Item 2: weights.field moved from OPEN to domain-lemma-proved, NPH_R22FieldSites (L103).** Its three index operations are ok for i < 64 (domain_ok). The domain is now stated at every located site:
- the literals 0..6 of finish_relation_round, the Horner polynomial and FIn_ExtractFuns (literal_sites);
- the finish dot under len weights ≤ 64 (dot_site);
- the claim dot under l < 64 (claim_site).

Two producers are not composed, and they are the residual of this definition:
- the weights length at the deployed tx2 finish call. That accumulator is the op9 flush of the op6 query-loop result. The closure states 64 only on an accepted-run witness (FIn_WeightLength.twelve) and at reached query states (NFS_QueryInvariant.Domain.width).
- the claim-dot iterator bound.

This is not fail/fail: a wrapped window can be valid (for example i = 2^59 gives the window [0, 32)).

**r24_canonical_mul** stays as recorded: a source-refinement obligation with no frozen counterpart.

Not changed: no ops interface, merged module, closed-row statement, field premise, trust row or contract. Every moved definition records its previous judgment under `nph_judgment_before_item1bin`, `_item3vo`, `_item4prep` or `_item2wf`.

<<reliances>>
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
| NPH_REFS7.json (backward screen, NPH_refs4_host.py with NPH_REFS7_SPEC.json, this run) | the direct definition referrers of the traversal: binary_step only from level_rows, level_rows only from levels, levels only from verify_owned and Port9OR_P6Verify.factored (= verify_owned by rfl, Port9OR_P6Verify.source_factor), verify_owned only from Port4B_VerifyInstall.verify; expandValues from nativeValues, withValues and NDO_JFw_Row.runRow; the referrers of finishConcreteField, FIn_Primitives.field and ClaimParser.field. Same positive controls as NPH_REFS6.json | binary_step (b) and values_owned_reference (b), this run |
| Call-site bindings of the two expandValues sites (gate text) | that the arguments of the compact expand call and the prepare op11 call are the range reads named in compact_site and installed_y1_site, and that NDO_JFw_Row.runRow (a copy of the compact row body, payload input[i1, i1 + size/2)) is covered by the same argument | values_owned_reference (b), this run |
| Executed prepare record (closure reading) | that the executed candidate.prepare runs on DrvC_Installation.currentInstalled cfg or its op8-guarded form (NPH_R22JoinCW6.installed_prepare_guarded) | prepare (b), this run |

<<wording>>
> **CheckedVsWrapping (R22, OPEN).** The gate's emitted bodies for the reached definitions are checked translations, in which an overflow is an error result. The deployed ELFs (f8c0ec72…, 63ad3e9c…, built from 4bb3b3f) wrap. The theorem transfers to the deployed binary when every executed checked or mixed definition meets one of three conditions: its checked body is total on every input (TOTAL); it is total on a domain that its reached callers are proved to supply ((b)); or wrapping acceptance is proved to imply checked acceptance directly (DIRECT). R22TotalCheckedComposition then gives safety of every executed checked operation and equality of the wrapping and checked results, under the P6/P7 interpretation of the operational tree as the compiled code.
>
> Status at 4bb3b3f (NPH_, evidence/r22-final-20261110/NPH_R22_FINAL_COUNTS.md): there are 225 checked or mixed definitions. 28 of them are proof-only references, excluded under lead ruling 1 on textual referrer screens. Of the 197 executed, 72 are TOTAL, 52 DIRECT and 71 (b); 1 has its domain lemma proved at every located site with the caller join open; 1 is open. 44 of the 393 CLOSED rows these definitions serve depend on a definition that is not closed. No reachable input on which the wrapping binary accepts and the checked model rejects is known. The Merkle traversal subtraction, the one site where such an input could have arisen, is proved safe on every reached state (NPH_R22Binary).
>
> Residual: weights.field's two producers (the finish-dot weights length at the deployed tx2 finish, and the claim-dot iterator bound), and r24_canonical_mul, which has no frozen counterpart.
>
> Removal condition: every executed definition is in (a), (b) or (c) on the final replayed closure, and each textual screen of section 4 is either replaced by a Lean statement or accepted by the owner as a named review item. Otherwise the owner records R22 as a retained trust row, named in the claim's first sentence.

The 2021 figures (35 TOTAL / 63 ACCEPTED-ONLY / 48 OTHER of 146 statements) concern a different object and remain superseded for this row.
