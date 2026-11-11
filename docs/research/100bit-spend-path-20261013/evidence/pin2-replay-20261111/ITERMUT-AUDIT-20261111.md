# Mutable-iterator write-back audit: verifier side at PIN2 (c7593d23fdc)

Read-only audit, 2026-11-11. No edits and no compiles. The pinned source was read with `git show c7593d23fdc:` (extracted to the scratchpad by `git archive`). The closure sources are the 14,101 modules of the L187 plan (`evidence/prov-p9b-20261110/L187_PLAN_READ.json`). All 14,101 resolve to repository paths whose sha256 matches the plan (0 missing, 0 mismatched). I also scanned the 177 `.lean` files in `/Users/dominic/aspis-lead-infra/l187-closure/overlay-PIN2/` and 1,374 `.lean` files under the PIN2 evidence directories (pin2-w3a..w8, pin2-public-binding, pin2-replay, devnet-pin2, overlay-PIN2*).

Between 4bb3b3f and c7593d23fdc, the only verifier-side source changes are in `pair_forest_semantic_terminal.rs`, `pool_route.rs` and `r1_pool_adapter.rs`. `sampler.rs`, `transcript.rs`, `verifier.rs`, `candidate.rs`, `compact.rs`, `multiproof.rs`, `weights.rs` and all of aspis-core are byte-identical. Emissions made from 4bb3b3f therefore apply to the pin for every site below except the adapter.

## Verdict in one paragraph

The finding is real for the verifier. It is not new, and no model in the soundness closure is unsound because of it. Exactly one verifier-reachable function has the erased-region shape (a reversed mutable slice iterator): `sampler::low_base_p_digits` (crates/aspis-r1-cost-probe/src/sampler.rs:56-73, write at line 63). The verifier reaches it through `transcript::Transcript::scalar` (transcript.rs:25) → `sampler::gamma_sample` / `sampler::ordinary_sample`. Every fresh Aeneas emission of that function from the frozen source in the repository drops the write, all with exit 0. This includes the original tool, Aeneas sha256 959659a6, in prov-p5a PCWJ_E001 and prov-p3u PCVX_E012. The drop was first recorded and formally refuted as an equality on 2026-10-27: `XRp_LowSamplerObstruction.all_blocks_law_false`, L089, evidence/extraction-assoc8-20261027/XRp_HANDOFF.md.

No closure module contains that emission. A scan of all 14,101 closure sources plus the PIN2 overlays finds 0 occurrences of `Rev (core.slice.iter.IterMut …)`, of a DoubleEndedIterator instance on IterMut, or of the XRn reverse helpers. The closure models `low_base_p_digits` by `AspisR1Post25Sampler.Funs`. That is an Aeneas emission of a non-frozen rewrite crate (`r1_post25_sampler_extraction`, two indexed loops) whose write is explicit (`Array.update`). Its provenance against the pin is OPEN (NO_FRESH_EMISSION, latest prov-p6u PCXF_ALL_STATUS), and that obligation cannot be closed with the base tool because the base tool's emission of the frozen function is wrong.

Every other mutable-iteration emission in the closure gives the written value back. These are forward IterMut, Enumerate over IterMut, Zip over ChunksExactMut, IntoIterator for `&mut [T; N]` / `&mut Vec`, and split_at_mut. That covers 11 generated files with mutable markers, plus the hand-adapted Port5Q2 reader.

## Method and limits

- **Source enumeration (task 1).** Script `tools/enum_sites.py` in the scratchpad, over every `.rs` under the six named source trees at the pin. Patterns: `.iter_mut(`, `.chunks_mut(`, `.chunks_exact_mut(`, `.rchunks*_mut(`, `.split_at_mut(`, `.last_mut(`, `.first_mut(`, `.get_mut(`, `.values_mut(`, `.split_first/last_mut(`, `for … in &mut …`, and `for … in x` where `x` is bound with `&mut` type in the same file. 236 hits, plus a separate whole-pin grep for `_mut(…).rev()`. That grep finds only 4 reversed mutable sites in the whole pin: r0_transcript.rs:129, sampler.rs:61, and sampler.rs:140 and 155 (both cfg(test)).
- **Reachability (task 2).** By imports and callers from the verifier modules (sampler, fast_*, r1_wire, r1_semantic, transport, weights, transcript, verifier, candidate, multiproof, compact) and the program (lib, r1_pool_adapter, pool_route, deployment_ids). I used a name-based call-graph sweep and then checked every candidate by hand. Name collisions (`new`, `parse`, `begin`, `verify`, `challenge_reference_circle_point`) were resolved manually. The sweep over-approximates; the hand checks are the authority.
- **Emission check (task 3).** Each closure file with a mutable marker was classified as a generated emission (AENEAS header or emission chunk) or a hand model. Each generated loop body was then read for the `next_back … (some <new value>)` give-back and for the caller's use of the back function.
- **Not done.** No LLBC was scanned mechanically: the LLBCs are on the host only and this audit is read-only. The give-back semantics of forward IterMut also depend on the Aeneas library (and some hand-written) models of `IteratorIterMut.next`, `Zip.next`, `ChunksExactMut`, `into_iter` and their back functions. Those are library-model trust (HM-B class) and were not re-audited here.

## Task 1, 2 and 4: sites and verdicts

### A. Verifier crate (crates/aspis-r1-cost-probe), reached by the R1 verifier

| Site | Enclosing function | Shape | Closure model | Verdict |
|---|---|---|---|---|
| sampler.rs:61 (write line 63) | `low_base_p_digits`, closure#1 passed to `core::array::from_fn` | `quotient.iter_mut().rev()`: **erased-region class** | `AspisR1Post25Sampler.Funs` (docs/research/v8-r0-zk-20261009/lean/AspisR1Post25Sampler/Funs.lean), a non-frozen rewrite with indexed loops. Used by `AspisR1.NKD_Low.root` (TX1:159, evidence/sampler-transcript-20261108/NKD_generated/NKD_Low.lean), which takes a native trace cut as hypothesis. Provenance OPEN (NO_FRESH_EMISSION). | **Closure model gives back. The frozen-source emission DROPS the write** (model unsound if that emission were used). It is not in the closure. In scope: the provenance row stays OPEN and the base tool cannot close it. |
| sampler.rs:91 | `add_small_base_p` | `for digit in digits` with `digits: &mut [u32; 8]` (forward IterMut) | `AspisR1Post25SamplerIndexedAddSmallCandidate.Funs` (indexed rewrite), used by `NKD_Add.root` (TX1:155). Provenance OPEN. | **Give-back present** in the closure model. Fresh frozen emissions also give back (quotes below). |
| verifier.rs:226 | `BatchedWeights::finish` | `weights.iter_mut().enumerate()` | `S8Kani2MutableSource` (generated from the isolated crate `aspis_r1_semantic_call_extraction`, with hand-inserted `nextWithBack` helpers), plus hand ports Port3_NativeFlushBody and Port4D_*. Provenance OPEN (NO_FRESH_EMISSION). | **Give-back present** |
| verifier.rs:243 (line 244 body) | `update_residue_row` | `for limb in row` with `row: &mut [u64; 4]` | `NEI_PushRaw.Funs`, `NEG_PushActual.Funs`, `NEG_RowIsolated.Funs` (isolated crate `neg_isolated`). `NEI_PushRaw_Funs.update_residue_row_loop1.body` is EQUALITY_PROVED (rfl) against the fresh 4bb3b3f emission with aeneas-b59d5188-extended (prov-p4a, eq/PRVEq_NEI_PushRaw_Funs.lean). | **Give-back present** |
| verifier.rs:364 | `read_checkpoint_weights` | `for out in &mut weights` (`Vec<K>`) | `Port5Q2_ReaderWeights` (hand-adapted emission text; its source lines 363-371 match the pin). | **Give-back present** |
| candidate.rs:257 | `prepare` (stage 1) | `logical.split_at_mut(LOGICAL_SEMANTIC)` (mutable split, not a loop) | `NMP_prepare.Funs`, `NHL_EmittedPrepare`, `NHW_EmittedPrepare`, `CurrentCompactCallerModelV1`. Provenance OPEN (WRONG_BASIS / NO_FRESH_EMISSION). | **Give-back present** |
| compact.rs:131 | `expand_values` (called from `prepare`) | `out.chunks_exact_mut(32)` zipped | Hand model `compact.expand_values` in evidence/slice-d-check-20261104/NFU_LPl_Kit_FunsExternal.lean:456 ("P6 OPEN", reference-based). No Aeneas body. | Not an emission; the write is modelled as an explicit output list. Outside the bug class. |
| multiproof.rs:174 | `verify_in_place`, `Arity::Eight` arm | `children.iter_mut().enumerate()` | `verify_in_place` is CANNOT_EXTRACT (breaks to outer loops; 4.9 table, 14k). The verifier calls it only with `Arity::Two` (candidate.rs:202), so this arm is dead at runtime. | Not in scope (no emission; arm unreachable) |
| weights.rs:353 | `Weights::materialize` | `w.iter_mut().enumerate()` | Called only by prover.rs:255 and sim.rs:345 (prover / r1p-check). | Not in scope (prover side) |
| semantic_wire.rs:270 | `begin` (legacy P2 `semantic` module) | `zc.iter_mut().enumerate()` | The R1 verifier uses `r1_wire::begin` and `r1_semantic`; nothing in the verifier modules references `crate::semantic` or `semantic_wire`. | Not in scope |
| r1_wire.rs:521, 651 | `record_parser_tests` / `prefix_parser_tests` | `chunks_exact_mut` | cfg(test) | Not in scope |
| sampler.rs:140, 155 | `qm31_index_tests::old_sample` / `old_pass` | `iter_mut().rev()` | cfg(test) | Not in scope |
| sim.rs:277, 278, 287; prover.rs:641, 679; host_commitment.rs, host_semantic.rs, host_sumcheck.rs | prover / `r1p-check` features | various | none in closure | Not in scope (prover side) |

### B. aspis-core and aspis-statement, reached by the verifier or adapter

| Site | Function | Shape | Closure model | Verdict |
|---|---|---|---|---|
| aspis-core/src/field/wide_exact.rs:275 | `WideExact::to_le_bytes` | `bytes.chunks_exact_mut(4).zip(self.to_limbs())` | `AspisR1WideToBytesSource.Funs` (source-cut crate; source lines 273-279 match the pin). Provenance OPEN (FAILED fresh compare). Lib models in `.FunsExternal`. | **Give-back present** |
| aspis-statement/src/pool_v1/pair_forest_accounts.rs:295 | `decode_pool_v1_pair_forest_master_v1` (adapter `decode_master_box`, r1_pool_adapter.rs:431) | `last_checkpoint_lane_sequences.iter_mut().enumerate()` | NJI extraction: the decoder bodies were omitted after a missing `Iterator.any` warning (NJI-F1, tool exit 0; evidence/tx2-decoders-20261108/NJI_HANDOFF.md). TX2:152/153 are OPEN; NJI_MasterModel and NJI_MasterIteration are hand models. | No emitted body (OPEN). Outside the bug class. |
| same file :463 | `decode_pool_v1_pair_forest_checkpoint_v1` (adapter `decode_checkpoint_box`, :439) | `lane_sequences.iter_mut().enumerate()` | Same omission. `NJI_CheckpointLoop` is a hand frame model with the write stated explicitly (`Frame … if j=k then target`). TX2:201/203 OPEN. | No emitted body (OPEN). Outside the bug class. |

### C. Program crates

| Site | Function | Closure status | Verdict |
|---|---|---|---|
| programs/r1-cost-probe/src/r1_pool_adapter.rs:495 | `decode_lane_from_pool_release` (stage-2 op50) | CANNOT_EXTRACT (early returns in loops; patch A then "could not match the contexts"). The hand transcription `evidence/prov-p3t-20261110/PCVV_LaneDecodeRef.lean` (`frontierLoop`, lines 61-75, 157-191) builds the frontier element by element. It is not in the closure: `RSL_TX2_217` takes op50 as a parameter. The LaneDecode trust row was refused, so this stays OPEN. | No emission. Outside the bug class. Still OPEN. |
| r1_pool_adapter_original.rs:495; adapter_rw_tests.rs; r1_checkpoint_tests.rs (8 sites) | test-only (`#[cfg(all(test, feature="pool-adapter"))]`) | none | Not in scope |
| programs/aspis-upload/src/lib.rs:161 | `write` | `data.get_mut(start..end)` is a range borrow followed by a copy, not an iterator | Not the class |
| programs/aspis-pool/src/pair_forest.rs:606 (`decode_lane_account_from_program_invariant_v1`), pair_state.rs:412 (`decode_from_program_invariant`); ~40 test `accounts.iter_mut().map(TestAccount::info)` | Pool program | The pool crate is not extracted (14q). Pool behaviour enters through trust rows, hand models or L159. | Not in scope (no emission) |

### D. In the closure but not on the R1 verifier path

| Rust site | Closure emission | Give-back | Why not in scope |
|---|---|---|---|
| aspis-core/src/transcript.rs:413, `Transcript::challenge_qm31` | `AspisR72Sampler.Funs` = evidence/prov-p2d-20261109/inputs/gate_AspisR72Sampler_Funs.lean:752-830 | **Present** | The R1 verifier uses only `HashFn` and `circle_fallback_point` from aspis_core::transcript. `circle_fallback_point` (transcript.rs:286-296) does not call `challenge_qm31`. |
| aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:522, `add_value_lanes` (`for residual in &mut range`) | `RPu_FIq_Native09` `add_value_lanes_loop3` (probe crate `aspis_r1_mask_extraction_probe`), EQUALITY_PROVED by P3c with tool 959659a6 | **Present** | The R1 verifier imports only `r0::Public` / `public_bytes` from this module. This branch is also `#[cfg(not(feature="pool-v1-pair-forest-packed-range-audit"))]`, and the program build enables that feature through `optimized-terminal` (programs/r1-cost-probe/Cargo.toml). **Flag:** the probe models the branch that is compiled out of the deployed program. That does not matter here, but whoever relies on FIq for add_value_lanes should check the feature set. |

### E. Every other site in aspis-core and aspis-statement

There are 116 non-test sites, listed in `appendix_nontest.txt` in the scratchpad. They are in R0, V6 or V7 legacy, state-only, prover or trace-builder code, and none is referenced from the R1 verifier or program modules. No closure module emits any of them with a reversed mutable iterator: the closure scan found 0 such shapes. All are **not in scope**.

One shape twin needs a note. `aspis-core/src/r0_transcript.rs:129` (`base_p_digits`, `rank.iter_mut().rev()`, write at :131) has the identical erased-region shape. The R1 verifier uses only `queries_from_pairs` and `CircleRow` from that module, so it is not on the verifier path today. If anyone extracts `aspis_core::r0_transcript::{qm31_sample, ordinary_sample}` with the base tool, the same silent drop will happen.

## Task 3: the Lean, quoted

**1. Frozen-source emission of `low_base_p_digits`: write dropped (not in the closure).** evidence/prov-p5a-20261110/PCWJ_E001_emitted/raw/PCWJ_post25/Funs.lean:243-271. Aeneas 959659a6 ("original"), frozen 4bb3b3f, Charon LLBC sha256 8c10e6c4…, aeneas_exit 0.
```
def sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  (iter : core.iter.adapters.rev.Rev (core.slice.iter.IterMut Std.U32)) ...
  let (o, iter1, next_back, _) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT Std.U32) iter
  ...
    let _ ← dividend / i3
    ...
    ok (cont (iter1, fun r => let r1 := next_back r
                              back r1, remainder1))
```
`next_back` is applied with no new value, and the quotient is bound to `_`, so the binary's `*limb = dividend / P` is lost.

The same body appears in:
- evidence/prov-p3u-20261110/PCVX_E012_emitted/raw/PCVX_tx2s/Funs_nosorry.lean:2463-2490: the whole-stage-2 emission, Aeneas 959659a6, LLBC sha 8c371d81…, frozen 4bb3b3f.
- evidence/extraction-assoc10-20261027/XRr_L017/sources/XRr_generated/XRn_Join_Funs.lean:3596-3627, through the `XRn_Join_reverseNext` wrapper, which restores the old `v` and discards the item give-back: `ok (v,⟨i⟩,fun r => ⟨restore r.iter v⟩,fun r item => ⟨restore r.iter item⟩)`, and the body binds the 4th component as `_`.
- evidence/emission-repro-20261110/NMH_E021_emitted/raw/NMH_sampler/Funs.lean.

The XRp packet already states it: "The frozen Rust writes the quotient limb. The selected emitted closure computes/divides but discards the quotient" (XRp_HANDOFF.md:18-19). Concrete block `ff ff ff 7f ‖ 0^28`: emitted `ok(eight zero digits, 2147483647)`, while the candidate quotient is ≤ 256 (L089, L098).

**Correction to the record.** The PCWJ_HANDOFF.md summary (P5a, line 6) describes this as a source-shape difference ("two explicit loops versus from_fn with an iter_mut closure"). The real cause is the dropped write in the frozen emission. That entry should cite L089 and this finding.

**2. Closure model of `low_base_p_digits`: write explicit.** AspisR1Post25Sampler/Funs.lean:149-187 (in `qm31_div_pass_loop.body`: `let rank1 ← Array.update rank j1 i5`; caller: `let (rank2, digits1) ← sampler.low_base_p_digits_loop1 rank1 digits 0#usize`).

**3. `add_small_base_p`.** Fresh frozen emission, PCVX_tx2s/Funs_nosorry.lean:2667-2720 and XRn_Join_Funs.lean:3474-3529:
```
    ok (cont (iter1, fun im => let im1 := next_back im (some digit1)
                               back im1, addend1))
  ...
  let digits1 := into_iter_back back
  ok (addend1 != 0#u32, digits1)
```
Closure model (indexed): `let digits1 ← Array.update digits i i6` (AspisR1Post25SamplerIndexedAddSmallCandidate/Funs.lean:24-44).

**4. `BatchedWeights::finish`.** docs/research/100bit-spend-path-20261013/lean/S8Kani2MutableSource.lean:229-273:
```
    ok (cont (iter1, fun e => let e1 := next_back e (some (i, w))
                              back e1))
  ...
  let im1 := enumerate_back back
  ok (iter_mut_back im1)
```

**5. `update_residue_row`.** evidence/slice-q-mul2-20261101/NEI_PushRaw/Funs.lean:81-89, 123-126. NEG_PushActual and NEG_RowIsolated are byte-identical in this range.
```
    ok (cont (iter1, fun im => let im1 := next_back im (some limb1)
                               back im1))
  ...
    let back ← update_residue_row_loop1 iter (fun im => im)
    ok (into_iter_back back)
```

**6. `read_checkpoint_weights`.** docs/research/100bit-spend-path-20261013/lean/Port5Q2_ReaderWeights.lean:30-37, 64-72:
```
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, reader.«at»))
  ...  (error arm) let im := next_back iter1 o   -- original value, matching Rust's early `?` return
  ...  let weights1 := into_iter_back back
```

**7. `candidate::prepare` split_at_mut.** evidence/tx1-observed3-20261110/NMP_L082/sources/NMP_generated/NMP_prepare/Funs.lean:300-326 (identical shape in NHL/NHW_EmittedPrepare:42-61 and CurrentCompactCallerModelV1:215-235):
```
    let ((semantic, y1), split_at_mut_back) ← core.slice.Slice.split_at_mut s i
    let (r2, semantic1) ← NMP_call_10 s1 semantic
    let (r3, y11) ← NMP_call_11 s2 y1
        let s3 := split_at_mut_back (semantic1, y11)
        let val1 := deref_mut_back s3
```

**8. `WideExact::to_le_bytes`.** docs/research/100bit-spend-path-20261013/evidence/s5-to-bytes-source-cut-v1/generated/AspisR1WideToBytesSource/Funs.lean:96-151:
```
    let chunk1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 chunk s
    ok (cont (iter1, fun z => let z1 := next_back z (some (chunk1, limb)) back z1))
  ...
  let cem1 := zip_back back
  let s1 := chunks_exact_mut_back cem1
  ok (to_slice_mut_back s1)
```

**9. `Transcript::challenge_qm31`** (section D). gate_AspisR72Sampler_Funs.lean:775-776, 811-813: `next_back im (some limb1)`, then `iter_mut_back back` → `to_slice_mut_back s1` → indexed reads.

**10. `add_value_lanes_loop3`** (section D). evidence/prov-p2b-20261109/inputs/gate/RPu_FIq_Native09.lean:346-347, 397-402: `next_back im (some residual1)`, then `into_iter_back im1`.

**11. PIN2 gate modules.** `PIN2_NEWGATE_r0` (1,389 lines), `PIN2_NEWGATE_r1_semantic` (227 lines) and `PIN2_NEWGATE_verifyprefix` (988 lines) contain 0 `rust_loop` definitions and no mutable iterator types; r0 has only shared `core.slice.iter.Iter`.

The named gate families contain no mutable iteration of any kind: AspisR1PublicPreparation.*, AspisR1PublicSerializer.*, R0P.* (61 modules), AspisR1FinishRelationCurrent, AspisR1PrefixAggregateParser and NMW_* (9 modules). In the FIq family, the only hits are Native09 (item 10) and its NativeExternal `into_iter` model; Native14's `Rev` is over `Range` and a by-value `IntoIter`, which is not the class.

## Consequences and next steps

1. **Soundness closure.** No closure module currently contains a dropped-write emission, so the PIN2 headline theorems are not invalidated by this finding.
2. **Open provenance obligation.** The low_base_p_digits, ordinary_sample and gamma_sample keys (AspisR1Post25Sampler.*, AspisR1GammaCaller.sampler.gamma_sample) stay OPEN. The base tool (959659a6) cannot discharge them, since its emission of the frozen function is provably different (L089). The only routes are:
   - a translator that rejects or correctly handles erased-region mutable borrows (the privacy stream's pre-pass, which rejects only and does not translate);
   - a proved refinement from the Rust to the indexed rewrite;
   - the native-cut route NKD already uses (TX1:159 root with a `LowTrace` hypothesis).
   No trust row is appropriate under the 2026-11-10 owner decisions. This adds a "silent write drop" entry to the translator lane, alongside op50 and the other 4.9a items.
3. **Gate for future crediting.** Every future fresh = gate run must apply the erased-region pre-pass, or must fail on `Rev (… IterMut …)` / `next_back` with a single argument. If it does not, an emission of `Transcript::scalar` or `tx2` that inlines the sampler could become a "fresh" side carrying the drop. PCVX_tx2s already contains it, but nothing was credited from it for the sampler. Every sampler key in the prov-* status files is OPEN, FAILED or NO_FRESH_EMISSION; none is EQUALITY_PROVED.
4. **Twin shape.** `aspis_core::r0_transcript::base_p_digits` (r0_transcript.rs:129) has the same shape and must go through the same pre-pass if it is ever extracted.

## LLBC files recorded for a mechanical pre-pass (host paths)

W8, PIN2, frozen c7593d23fdc, docs/research/100bit-spend-path-20261013/evidence/pin2-w8-20261111/PW8_E00n_emitted/PW8_E00n_PINS.json:

| Run | Host path | LLBC sha256 | Tools | Roots |
|---|---|---|---|---|
| E001 | `/home/dombarker/project-offloads/codex-pc-pin2-w8-20261111/PW8_E001_emitted/repro.llbc` | `e6e46310d7b7e02b4e83fdca571e464fb6e9b748edf7bcc21ab6679ef0973818` | Charon 454586e9 / Aeneas 0d21a9ec | verify_observed, semantic_validated, begin, public_transcript, public_bytes |
| E002 | `…/PW8_E002_emitted/repro.llbc` | `2062e66afa761483546f0974f91af50b43334e13b3983b93283f1f4a0d10b484` | same pair | from semantic_validated |
| E003 | `…/PW8_E003_emitted/repro.llbc` | `d674d1511682efeb0ad5fce5e02ff428cb86aace0d5bbf65b3f5ac0e14a12ac7` | fe80: Charon daad69be / Aeneas b59d5188-extended | verify_observed |
| E004 | `…/PW8_E004_emitted/repro.llbc` | `41ae76067cca887964bc0b6fe68d9cfd8e3bdea897e760ab200473bfbc256d2c` | 0d21a9ec pair | semantic_validated, …, Verified, SecureCirclePoint |

None of the W8 roots reaches `Transcript::scalar`. A verifier-wide pre-pass needs an LLBC rooted at `verifier::tx1` / `tx2` / `tx2_authenticated`, such as PCVX below.

Stream C (frozen 4bb3b3f unless noted):

- **prov-p3u PCVX_E012/E013:** `/home/dombarker/project-offloads/codex-pc-prov-p3u-20261110/PCVU_stable/all.llbc`, sha `8c371d81281bb22e8fe4c803e9eed0e76e135324ce0a05d87ef86294b6428803`, whole tx2s path. This is the best existing input for a verifier-wide pre-pass, and it contains the sampler.
- **prov-p5a PCWJ_E001/E003/E004/E005**, sampler roots ordinary_sample and qm31_sample: `/home/dombarker/project-offloads/codex-pc-prov-p5a-20261110/PCWJ_E00n_emitted/repro.llbc`, shas `8c10e6c4…08e3`, `6edf4398…c908`, `afd1b079…a6f0`, `3b872037…ad64`.
- **prov-p3t PCVV, adapter (4.9a):** `PCVV_E001_emitted/repro.llbc` on the host under `/home/dombarker/project-offloads/codex-pc-prov-p3t-20261110/`, sha `9d82b7f3c9abff96304c78258f831d7a77e998116b2ee708f5ccd2791bf7bbaa`.
- **prov-p9a PCXQ_E001..E009**, revision 271869c946d (a PIN2 ancestor; the verifier-side diff to c7593d23fdc is prover-only): `/home/dombarker/project-offloads/codex-pc-prov-p9a-20261110/PCXQ_E00n_emitted/repro.llbc`.

  | Run | sha256 | Roots / tool |
  |---|---|---|
  | E001 | `b38dbf64…2f1f` | public_bytes |
  | E002 | `ce1c2fcb…5ffa` | r1_pool_adapter::process, pool_route::admitted (original tool) |
  | E003 | `c93b5f65…5f3a` | close_checkpoint (original) |
  | E005 | `60c84cae…334b` | close_checkpoint (second) |
  | E009 | `95c45fb9…aa27` | semantic terminal |
  | E004, E006–E008 | none recorded | — |

- **prov-p9f PCXU_E001..E003**, frozen c7593d23fdc, roots public_transcript and public_bytes, paths `/home/dombarker/project-offloads/codex-pc-prov-p9a-20261110/PCXU_E00n_emitted/repro.llbc`.

  | Run | sha256 |
  |---|---|
  | E001 | `589d7085…9290` |
  | E002 | `165f993e…b24c` |
  | E003 | `d5ccbe5e…a227` |

- **prov-p9h PCXW:** probe crate, not frozen source. `/home/dombarker/project-offloads/codex-pc-pin2-probe-20261111/PCXW_llbc/PCXW_E001.llbc`, `PCXW_E004.llbc`, `*_m31.llbc`, and `/home/dombarker/project-offloads/codex-pc-prov-p9h-20261110/PCXW_E00n_emitted/repro.llbc`. No LLBC sha is recorded in the repository receipts.

## Status

Established: no dropped-write emission is in the PIN2 soundness closure, and every closure emission of a mutable loop or split gives back its writes. One verifier site, `sampler::low_base_p_digits`, is affected at the tool level. Its frozen emission is wrong under 959659a6 (exit 0), as already refuted on 2026-10-27, and its provenance row stays OPEN.

Not established: a mechanical pre-pass over a verifier-wide LLBC (not run; host only), and the HM-B library models of the IterMut, Zip and ChunksExactMut back functions (not re-audited).

target not yet established
