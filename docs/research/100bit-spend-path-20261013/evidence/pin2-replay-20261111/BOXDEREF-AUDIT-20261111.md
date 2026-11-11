# Box deref-temporary write audit: verifier side at PIN2 (c7593d23fdc)

Read-only audit, 2026-11-11. No edits, no compiles, no host access. Source: the pinned tree extracted in the scratchpad (`pin/`; spot-checked sha-equal to `git show c7593d23fdc:` for candidate.rs, r1_pool_adapter.rs, r0/onchain.rs). Scope classes reuse ITERMUT-AUDIT.md. The counterexample was not reproduced here.

## Trigger, as used for the enumeration

rustc's Derefer pass (by reading rustc, not tested) puts a `CopyForDeref` temporary in front of every `Deref` that is not the first projection of a place. A Box-typed temporary therefore appears for a write `X.f.y = v` or `&mut X.f…` whenever `f: Box<_>` is reached after another projection. That covers `b: &mut Box<S>` (the reported case), `s: &mut S` with a Box field, and also an owned local struct with a Box field (`s.f.y = v`). I enumerated all three. A write through a local Box binding (`b.y = v`, `b[i] = v`, `*b = v`) has its Deref at projection 0, so it is **not** split and is not this class. Those sites are listed separately. Per the report, the trigger fires only in dependency crates (aspis-core, aspis-statement, and aspis-r1-cost-probe when the program crate is extracted). All 360 Charon receipts in the repository evidence use `--mir built` for the crate under extraction.

## Result

**The pinned verifier side has 0 sites of the reported class.** No `&mut Box<T>` parameter exists anywhere in the six trees (grep `&\s*mut\s+(alloc::boxed::)?Box`: 0 hits, tests included). The Box fields that are on the R1 path are only constructed, moved out (`*common`, `*live_snapshot`) or read. They are never assigned or mutably borrowed.

| Site | Function | Crate (MIR) | Access | Scope class | Verdict |
|---|---|---|---|---|---|
| r1_pool_adapter.rs:154-157, 161, 166 (struct fields) | `authenticate_asq8_accounts` builds them (:703, 728, 744, 760, 768-776); `asq8_common` :818-823; `reconstruct_asq8_statement` :862, 871; `scan_proof_buffer` :791-806 | program crate (local, built MIR) | construct, then read only (`authenticated.master.identity.asset_id`, `*authenticated.live_snapshot`) | extracted scope (adapter; AspisR1AdapterReconstruct) | no write; not the class |
| r1_pool_adapter.rs:240, 430, 438, 510, 814, 833, 847 | `decode_public_statement_box`, `decode_master_box`, `decode_checkpoint_box`, `decode_lane_from_pool_release`, `asq8_common`, `transfer/withdrawal_statement_box` | program crate | `Box::new(value)` then return or `&statement` read | extracted, or CANNOT_EXTRACT (op50, :450) | no write |
| r1_pool_adapter_owned.rs:318 | owned `authenticate_asq8_accounts` (:230), `live_snapshot` | program crate | construct, read | extracted scope | no write |
| r1_semantic.rs:11 `claims: Box<[[QM31;29];3]>` | read at verifier.rs:59 (`prepared_claim`, `sem.claims[point][l]` via `&Verified`) and r1_semantic.rs:248-254; moved at eight_way.rs:120 | cost-probe (local for verifier emissions; dependency only when the program crate is the root) | read only | extracted scope | no write. A read through the Box copy is not affected. |
| r1_semantic.rs:42-54 `claims` | init via `heap::uninit` + raw `as_mut_ptr().cast().add(p).write(..)` (:47-50) | cost-probe | raw-pointer write, not a Box deref temp | cannot-extract (unsafe); the closure uses the non-frozen rewrite `ClaimsUnrolledParentSource` (provenance OPEN, prov-p6u PCXF_NONFROZEN.md:16, 44) | not the class |
| r1_wire.rs:355-371 `point_claims_boxed` | raw-pointer init (:363-365) | cost-probe | raw pointer | dead (no caller anywhere in the pin) | not the class |
| candidate.rs:255-264 `prepare` -> `Box<Prepared>` (built at verifier.rs:88 `Prepared::new`, :431 `resume`) | `tx1` :278, `tx2_common` :297 use `&p` only | cost-probe | construct, read | extracted (NMP_prepare / RSL_TX1_087, provenance OPEN per prior audit) | no write. `logical` (:256) is a `Vec`, not a Box. |
| eight_way.rs:108, 117 `tx1_finish` / `tx1_prepare` (`Box<Prepared>`, `Box<[[K;29];3]>`) | owned, `&p` reads, move | cost-probe | read / move | dead feature arm (`audit-eight-way`, verifier.rs:526; compile_error with program-build, lib.rs:45-46) | no write |
| weights.rs:202-206 `box_from_parts` / `Weights::new` | callers prover.rs:252 and sim.rs:343 only | cost-probe | construct | prover-only | no write |
| semantic.rs:11, 34; semantic_wire.rs:210 | legacy P2 `semantic` module | cost-probe | raw ptr / read | outside the closure (not on the R1 path, per prior audit) | not the class |
| aspis-core r0/heap.rs:11-21 `uninit` | `Vec` -> `into_boxed_slice` -> `into_raw` / `from_raw`; no deref | aspis-core (dependency, optimized MIR) | none | extracted path (callers above) | no write through the Box |
| aspis-statement pair_tree_profile.rs:662-746, pair_forest_terminal.rs:332-398 (`*_boxed_v1` decoders) | `Box::new(decode(..)?)`, then `*live_snapshot` / `*common` moved out | aspis-statement (local in AspisR1TerminalDecoder, crate header `[aspis_statement]`; dependency at optimized MIR in PCWE_E003 / adapter runs) | construct, move | extracted scope (TX2 decoders) | no write |
| aspis-statement pair_forest_semantic_terminal.rs:1271 (`composition_parts`), pair_forest_copy_terminal.rs:169, payment_semantic_terminal.rs:254 (`boxed_at_point`) | `Selectors::boxed_at_point(point)` then `&selectors` reads only | aspis-statement (dependency) | construct, read | verifier path via `r0::Public::terminal_qm31` (r1_semantic.rs:248) | no write |
| aspis-core r0/onchain.rs:21, 24 (`Box<OpeningData>`, `Box<V1Invariants>`); onchain_re3.rs:22, 25; onchain_unhoisted.rs:22 | raw-pointer init (onchain.rs:52-57, 68-81); `v1.alpha_powers = ..` on a **local** Box (onchain.rs:112, onchain_re3.rs:98) | aspis-core | local-Box write (Deref at projection 0) | outside the closure: R0 only; callers are aspis-statement/src/r0.rs:144-298, which the R1 crates do not import | not the class |
| aspis-core verify.rs:1036 `Option<Box<ExactWideCombinationWeights>>` | `.as_deref()` read at :1293 | aspis-core | read | outside (legacy `aspis_core::verify`, not imported by R1) | no write |
| aspis-core v6_transcript.rs:466/471, 569 | `claims[row][column] = value` on a local Box | aspis-core | local-Box write | outside (V6 legacy) | not the class |
| aspis-statement pair_forest_copy_builder.rs:212-217, 361-366 | local Box arrays written by index | aspis-statement | local-Box write | outside (trace/prover builder) | not the class |
| aspis-statement state_only_verify.rs:106-108, 1215-1216; state_only_spend.rs:108-110 | Box fields, construct and read | aspis-statement | none | outside (state-only legacy; not imported by R1) | no write |
| programs/aspis-pool (pair_state.rs:99, pair_dispatch.rs:67, pair_forest_dispatch.rs:37-38, pair_processor.rs:374/377, 532/535) | construct, reads, and `&mut next_image` coerced to `&mut [u8;N]` (local-Box reborrow) | Pool program | local-Box write | not extracted (14q) | not the class |

Sibling shape outside the Box class: r1_pool_adapter.rs:989-990 (`close_checkpoint`), `**checkpoint.try_borrow_mut_lamports()? = 0` / `= total`. That is a double deref through `RefMut<&mut u64>`, so the Derefer temporary has type `&mut u64`, not Box. It is in the program crate (local, built MIR). The report does not cover it. It is noted for whoever owns the close-path model.

## Emitted Lean (closure)

There are no in-scope write sites, so there is nothing that could be lost. For the Box-bearing extracted functions, the emissions return the constructed value or read correctly:

- AspisR1AdapterReconstruct/Funs.lean:2251-2268 (`r1_pool_adapter.asq8_common`): `ok { …, output_lane := authenticated.selected_lane.lane_id, checkpoint_sequence := authenticated.checkpoint.checkpoint_sequence, …, lane_transition := { live_snapshot := authenticated.live_snapshot, candidate_afterstate } }`. Box is erased and the reads are correct.
- AspisR1TerminalDecoder/Funs.lean:2780-2786 (`decode_transfer_statement_boxed_v1`): `| Continue val => ok (core.result.Result.Ok (…PrivateTransfer common val))`. The value written by `Box::new` is returned.
- ClaimsUnrolledParentSource.lean:173-221 (non-frozen `candidate_claims::claims`, local-Box index writes): `let out := index_mut_back val2` … `let out1 := index_mut_back1 val3` / `let out2 ← Array.update out1 2#usize val4` / `ok (core.result.Result.Ok out2)`. All three writes are given back.

Mechanical scans of the closure (14,101 L187 sources plus 177 overlay-PIN2 files):
- Only 5 files contain `Box<` or `boxed::Box` at all. Two are generated (ClaimsUnrolledParentSource, quoted above, and its Types file); the other three are hand specs or comments (RSL_TX1_087:5, 59; RSL_TX2_217:5; RSL_Verifier:121, 223; NIW_AlignOwner:57). No generated file contains `alloc.boxed` or `Box.new`.
- Lost-write symptom scan (`def f (… p …) := ok p` or `ok (…, p)` as the whole body) over the 375 generated closure files: 43 hits, all benign. They are 28 `Clone.clone` (`ok self`), newtype getters (`FibreIndex.get`, `Q.limbs`, `M31_constructor`), stateless `FnMut` closures returning `(tupled_args != 0#u8, c)` (e.g. NJI_Extracted.Core.lean:494, 588), and reference wrappers (NDH/NDM/NGC `*_ref`). None of these corresponds to a Rust write. The list is in the scratchpad file `boxaudit/identity_hits.txt`.

## LLBC text search

No pretty-printed LLBC for PCVX (prov-p3u), PCWJ (prov-p5a) or PW8_E00x (pin2-w8) is present in the repository. The emitted directories hold only Lean, receipts and time/metadata `.xz` files, and decompressing every `.xz` there gives 0 `copy (*` lines. The LLBCs are on the host only (paths in ITERMUT-AUDIT.md, last section). The only pretty-printed (U)LLBC texts in the repository with `copy (*` are old and outside PIN2: r426 `original-ullbc.stdout` (13), r426 `R426-original-ullbc.stdout` (13) and s10-repin3 `frontier-frozen-bodies.txt` (39). Each has **0** hits whose target local is Box-typed (script: scratchpad `boxaudit/boxcopy.py`).

Charon receipts (360 under evidence/ and docs/.../evidence): every one uses `--mir built`. Dependency items pulled in transparently (read at optimized MIR) are aspis_core field/circle/merkle `parent_with_digest`/state_only_* helpers, `aspis_statement::…::r0::_::public_bytes`, `validate_pool_v1_pair_forest_terminal_statement_v1`, `encode_common`, `encode_pool_v1_pair_verified_afterstate_v1`, and digest canonical helpers. PCWE_E003 (prov-p4e) includes all of `aspis_statement`, starting from `reconstruct_asq8_statement`. No function in this set writes through a Box.

## Verdict

- Per site: every site is "no write through a Box", "not the class" (local-Box or raw-pointer write), or outside the closure. There is no in-scope site, so there is no give-back to check beyond the three emissions quoted.
- **The PIN2 theorem closure does not depend on any emission with a lost Box write.** The frozen verifier side contains no source site of the trigger, and the closure's generated files show no Box write at all apart from a correctly given-back local-Box write in ClaimsUnrolledParentSource.
- Limits: this is a source-level enumeration. It cannot see a Box-typed `CopyForDeref` that rustc's optimized-MIR passes might introduce in a dependency body (inlining, reference propagation) where the source has none. Closing that requires a mechanical scan of the host LLBCs (PCVX_E012 `all.llbc` 8c371d81…, PW8_E001..E004, PCWE_E003, PCXQ_E002) for Box-typed locals assigned from a copy of a deref place and later written. This was not run. The tool-level defect itself is unaffected by this audit: any future extraction of code with this shape (for example the Pool program, or a refactor that adds `&mut Box<_>`) would need the pre-pass or a rejection rule.

target not yet established
