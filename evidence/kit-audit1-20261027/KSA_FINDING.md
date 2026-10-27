# Worker-kit audit

Audit verdict: worker kit is not a faithful emission interface. No release premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 unchanged.

The definition-by-definition inventory is [KSA_INVENTORY.md](KSA_INVENTORY.md),
with exact hashes, raw-emission comparisons and ambiguity candidates in
[KSA_inventory.json](KSA_inventory.json). Text identity and semantic fidelity
are separate checks. An unproved adapter is UNDETERMINED even if fixtures pass.

Known failures retained: predecessor-indexed `XRn_Join_mpow`,
`XRn_Join_qpow`, and the supplied `aspis_core.field.M31.inv`.
The canonical-input inverse-two disagreement is already proved by
`XSd_InverseCompare.mismatch`; exponent-two collapse by LPo's closed diagnostic.
These concern stand-ins; no shipped Rust or adopted-root defect follows.

Budget cap: 60 Lean, 10 Rust, 0 Kani; one capped host scope at a time.
No shipped source change or ELF rebuild.

## Focused kernel stage

`KSA_L002` passes `KSA_Checks`: inverse-two mismatch, generic exponent-two
collapse, multiplication-two = four, zero/P byte-decoding probes and explicit
carrier roundtrip. All seven top theorems print standard axioms only.
`KSA_L001` was a root-directory argument error before elaboration; corrected
only this job's invocation configuration, not the shared runner.

## Import collision resolved

`KSA_L003`–`KSA_L018`, then `KSA_L020`, compile the 17 private kit copies.
`KSA_L019` failed on three explicit root-qualified compact calls and an
unclosed generated noncomputable section; the replacement prefixes those
names and closes the scope. It is not a resource-failed rerun.
`KSA_isolation.json` checks reverse-name-transform byte equality for every
source. Bodies are unchanged, including the defects; these are isolation
copies, not replacements offered for adoption.

`KSA_L021` successfully co-imports the complete prefixed kit with the unchanged
`LPn_DotClosed`, Claims/Decode/Expand endpoints. `KSA.windows_roundtrip` and
`KSA.windows_next` prove exact carrier roundtrip and next-operation transport
for the two Windows owners; both print only `propext`. This resolves the
`Windows.noConfusion` collision without modifying either predecessor.
The co-import does not itself establish transport of all nominal kit carriers.

## New counterexamples and retained scopes

`KSA_L028` proves the WHOLE kit selected-mask result on zero coefficients,
explicit one and point `[1,0,...,0]`: first limb `1424173332`. Frozen native
Rust returns `708712922` (`KSA_R002`/`KSA_R004`). Both other limbs are zero.
The replacement is `AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value`,
used by adopted `AspisR1.FIp_SemanticArithmetic.mask`; retain the canonicality
conditions in `AspisR1.FIp_MaskValue.source`.

`KSA_L029`/`KSA_L034` prove a second exact source discrepancy, now directly
against emitted `FIo_Native...WideExact.mul_qm31`. Set the wide value's low
quartic component to `(1,0,1,0)`, high component zero, and the multiplier to
`(4294967295,0,4294967295,0)`. The kit returns low limbs
`(3,1,2147483645,0)`; the emitted body and frozen native return `(3,1,2,0)`.
The kit omits the emitted `canonical_qm31` call. Use the emitted body at
`lean/FIo_NativeFuns.lean:409`, not another handwritten adapter.
No claim that this noncanonical operand occurs in an actual verifier run.

`KSA_L031` proves exact complete same-input Dot.push transport to the emitted
FIo operation for arbitrary accumulator words and operands. Its two new roots
have standard axioms only. This is positive operation evidence, not a
whole-prepared-claim, query-history, adoption or artifact proof.

Failed attempts remain excluded: L025 hit the default heartbeat limit; its
broad simplification was replaced by the symbolic even-spine lemma L027 and
the focused result L028. L026 was an invalid monadic definitional simplification.
L032 needed explicit closed reduction for an irreducible byte operation; L034
passes. No timeout or memory failure was rerun unchanged or at a larger cap.

Rust R001 failed on four missing immutable fixture files; R002 adds precisely
those frozen files and passes. R003's direct use of native field arithmetic
on a noncanonical counterpart overflows under the explicitly recorded checked
optimized profile. This is NOT a source/emission/production defect claim.
R004 replaces ONLY the diagnostic counterpart with the kit's literal wrapping
arithmetic and passes, while native WideExact itself remains frozen. Every
run validates the offline resolved graph against the unchanged frozen lock.

## Byte decoder failure

The eighth UNFAITHFUL definition is `aspis_core.field.QM31.from_le_bytes`.
The kit returns `ok none` on lengths 0 and 17; frozen Rust panics on the empty
slice and returns `Some zero` on 17 zero bytes. Kernel probes are in
`KSA_SmallBytes`; native R005 retains the unexpected panic, and R006 catches
that expected panic and passes both differential assertions. Both are source
behavior distinctions, not acceptance vulnerabilities or reached-input claims.
Use adopted `AspisR1.FIp_DotDecode.field.QM31.from_le_bytes` (line103).
The raw release Funs has no emitted body for this external. The existing
adopted decoder is a body copy of the emitted slice/Option program; its
name/import-only isolated copy and hashes are in KSA_decoder_provenance.json.

## Meaning and coverage of the verdicts

The inventory includes all 17 kit files, every definition in their handwritten
portions, all 15 nontrivial edited declarations among the 307 raw Funs bodies,
and every definition in the XRo_Join/XSd successor source modules. There are
279 rows: eight UNFAITHFUL, one FAITHFUL (Dot.push against the emitted body),
and 270 UNDETERMINED. UNDETERMINED explicitly includes definitions with no
fresh per-definition proof or native probe. This is not a certification that
every remaining stand-in was independently executed. The evidence columns
separate fresh checks, retained leaf gates, and unchecked obligations.
No whole-source fidelity, complete callback/borrow/effect transport or release
premise discharge follows from the small-input checks.

The source/statement dependency inventory covers 1,740 explicit theorem
spans in 850 merged modules. Two kernel environments inspect statement and
proof constants; 618 explicit theorem names are matched, with 360 paths to
unresolved kit definitions and 43 to refuted definitions. Another 678 theorem
spans are conservative import candidates outside those kernel environments.
They are fully listed, withheld from emission credit, and **not** asserted to
be exact kernel dependencies. Thus the exhaustive *per-constant* dependency
portion remains UNDETERMINED for those candidates; no import grep is promoted
to a kernel-use claim. Auto-generated equations and private constants are in
the raw edge receipts, including intermediary witnesses omitted from the
human theorem tables. Independently proved rejection facts and diagnostic
counterexample theorems retain their mathematical scope.

## Assumptions and release boundary

Discharged here: small arithmetic/byte counterexamples, a full Dot.push
operation transport, and the Windows ownership/import collision. Retained:
all source-to-artifact, native reachability, callback/trace/history, source
adoption and headline premises. Added/removed/changed release premises: 0/0/0.
No security metric, game, frozen3 model, RuntimePersistence trust, narrowed
D188 or owner-adopted root changes. Neither S2 nor the 100-bit target is newly
established. No shipped/cfg(kani) file changed and no ELF rebuild was triggered.
Inherited pins, not rebuilt: default
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
No wallet/key action, other worktree edit, push or merge occurred.

Concrete next work: use the emitted/adopted definitions named in the failure
matrix, preserve actual caller domains, and re-prove the affected associations.
Complete the individually marked UNDETERMINED stand-in checks and the remaining
kernel dependency candidates before granting any whole-kit emission credit.

## Failure matrix and required replacements

QM31 tuples list `(c0.a,c0.b,c1.a,c1.b)`; WideExact tuples list low then high
quartic limbs. A single counterexample refutes the unrestricted stand-in law,
without proving any actual-product reachability claim.

| UNFAITHFUL stand-in | Exact distinguishing input / result | Emitted or adopted definition to use |
|---|---|---|
| `XRn_Join_mpow` | Base2, exponent2 gives1 rather than4; inverse exponent gives2 rather than1073741824 | Do not expose as a source power; inverse consumers use `AspisR1.SAQ_Inverse.source`, the emitted fixed addition chain |
| `XRn_Join_qpow` | Every base at exponent2 gives one; base2 squared is four. At base275/exponent26 kit is1424173331 | Emitted `FIo_Native.aspis_core.field.QM31.pow` for u64 power; adopted R72 `QM31.try_inv` for inverse; selected-mask emitted chain for degree26 |
| `aspis_core.field.M31.inv` | Canonical2: kit `ok2`, adopted/native `ok1073741824`, both succeed | `AspisR1.SAQ_Inverse.source` / adopted `AspisR72Sampler.field.M31.inv` |
| `aspis_core.circle.secure_ood_circle_point_from_parameter` | Canonical t=(0,0,1,0): native x=(429496729,1288490188,0,0), y=(0,0,429496730,1288490188); kit x=(2107483647,2127483647,0,0), y=(0,0,60000000,2127483647) | `AspisR72Sampler.circle.secure_ood_circle_point_from_parameter` and its adopted wrapper adapters |
| `sampler.circle_sample.closure...call_once` | First fallback row installs exactly the above mismatching t; Second also differs, full limbs in R002/R004/R006 stdout | Adopted `AspisR1CircleFallback.transcript.circle_fallback_point`, via RPz7 wrapper's `transcript.circle_fallback_point` |
| `state_only_selected_mask_value` | c1=0, masks=0, explicit=1, point=[1,0,...,0]: kit first limb1424173332, native708712922 | `AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value`; adopted `AspisR1.FIp_SemanticArithmetic.mask`, retaining FIp_MaskValue.source's conditions |
| `WideExact.mul_qm31` | Wide low=(1,0,1,0), high=0; rhs=(4294967295,0,4294967295,0): kit low=(3,1,2147483645,0), emitted/native=(3,1,2,0) | `FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31`, `lean/FIo_NativeFuns.lean:409`, which already calls `canonical_qm31` |
| `QM31.from_le_bytes` | Empty slice: kit `ok none`, adopted emitted body `fail panic`, native panic. 17 zero bytes: kit none, native Some zero | `AspisR1.FIp_DotDecode.field.QM31.from_le_bytes`, `lean/FIp_DotDecode.lean:103`; KSA_EmittedDecoder is a checked names/import-only copy, not a new implementation |

## Final verification receipts

Used **43/60 Lean attempts, 6/10 Rust runs, 0 Kani**. Lean:34 pass/9 rejected;
Rust:3 pass/3 rejected. All66 explicit new theorem declarations have accepted
standard-only axiom prints. Every CURRENT new module matches an exit0 compiler
input; KSA_VERIFICATION.json reports zero errors. Failed/sorryAx diagnostics
are retained but never accepted. No wall timeout, memory kill or cap increase.
L036/L037's isolated empty-expand probe failed reduction/depth checks; it was
removed from the final small-byte module, whose other13 probes pass. The
existing LPl expand leaf is reused only within its documented scope.
L040 lacked an unrelated `PAln_RowBounds` object through FIo_Install. No shared
module/launcher was repaired: L041 copied the adopted decoder unchanged except
names and its import narrowed to the required existing FIo_NativeFuns; L042
proves the exact short-input mismatch. Decoder provenance is byte-checked.

Final focused target: `KSA_FinalAudit.lean`, KSA_L043, exit0,
wall3.895502678991761s, peakRSS5253080KiB, swaps0,
revision `b5e90d1856` plus the exact dirty source hash in its receipt.
All eleven selected top roots print `[propext, Classical.choice, Quot.sound]`.
Windows and Dot roots were separately co-import audited in L021/L031 with
standard axioms. No full manifest or unchanged regression was replayed.
Compiler-summed wall411.9660398210981s; maximum attempt RSS5426300KiB; total
swap0. Every individual target/argv, source revision/hash, dependency and Aeneas
object pins, exit, time, RSS, swap and axioms are in KSA_attempts.jsonl and the
original per-attempt receipt/stdout/time files. Rust1.94.1/e408947bf, optimized,
`-j4`, offline, frozen lock SHA256
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`;
resolved graphs and unchanged post-run lock hashes are retained for all6 runs.
Native runs used the explicitly recorded release overflow-check setting; the
R003 diagnostic overflow is excluded, and R004/R006 use literal kit wrapping
only on the comparison side. No native profile claim about the deployed ELF.

All scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64;
Lean `-j1 -M7000`. Admission code requires exit0 AND allowed:true; all recorded
reservations admit. No transport/admission retry was needed. Exact Aeneas
objects selected by LEAN_PATH are pinned per Lean attempt. The persistent a4
cache remains present, all346 baseline objects hash unchanged, private Lean
objects retained, no live owned scope. Only this job's Rust target directory
was removed. KSA_terminal_state.json records this terminal check.

## Complete definition inventory


Raw release `evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean`, SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`.

279 declarations: all definitions/carriers in non-emitted kit files, 15 edited Funs declarations, and XRo/XSd successor adapters. Unchanged emitted Types are excluded. `KSA_inventory.json` retains full source hashes, candidate paths, emitted-body text comparisons, and per-row validation/replacement status.

FAITHFUL is reserved for a complete scoped association, not a passing fixture. UNDETERMINED includes untested definitions and adapters whose whole source/effects/carrier law remains open. Native tiny-field fixtures are not a whole verifier proof.

| File:line | Definition | Shipped counterpart or model | Raw comparison | Verdict | Kernel check | Native check |
|---|---|---|---|---|---|---|
| XRn_Join_ABI.lean:5 | `XRn_Join_enumerateNext` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:14 | `XRn_Join_reverseNext` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:22 | `XRn_Join_nextBackPair` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:25 | `XRn_Join_intoIter` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:29 | `XRn_Join_fromFnState` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:33 | `core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.any` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:37 | `XRn_Join_revRestored` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ABI.lean:44 | `XRn_Join_enumerateRestored` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:6 | `XRn_Join_word` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:8 | `XRn_Join_q` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:10 | `aspis_core.field.M31.from_le_bytes` | crates/aspis-core/src/field.rs:239; crates/aspis-core/src/field.rs:409; crates/aspis-core/src/field.rs:1021 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L002 zero/P probes | KSA_R002 six boundary words; equality holds on tested inputs |
| XRn_Join_ByteFields.lean:13 | `aspis_core.field.QM31.from_le_bytes` | crates/aspis-core/src/field.rs:239; crates/aspis-core/src/field.rs:409; crates/aspis-core/src/field.rs:1021 | NO EMITTED BODY in raw Funs | UNFAITHFUL | KSA_L038/039 KSA.Bytes.qm_zero/qm_short/qm_long | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_ByteFields.lean:16 | `aspis_core.field.wide_exact.WideExact.from_limbs` | crates/aspis-core/src/field/wide_exact.rs:207 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.wide_limbs | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_ByteFields.lean:19 | `aspis_core.field.wide_exact.WideExact.to_limbs` | crates/aspis-core/src/field/wide_exact.rs:238 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.wide_to_limbs | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_ByteFields.lean:22 | `aspis_core.field.wide_exact.WideExact.from_le_bytes` | crates/aspis-core/src/field/wide_exact.rs:255 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.wide_bytes/wide_short | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_ByteFields.lean:26 | `XRn_Join_wordBytes` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:28 | `XRn_Join_qBytes` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:30 | `aspis_core.field.wide_exact.WideExact.to_le_bytes` | crates/aspis-core/src/field/wide_exact.rs:273 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.wide_to_bytes | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_ByteFields.lean:33 | `aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31` | crates/aspis-core/src/r0/scalar.rs:89 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.from_m31_p | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:37 | `XRn_Join_mpow` | library model | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_ByteFields.lean:44 | `aspis_core.field.M31.inv` | crates/aspis-core/src/field.rs:213; crates/aspis-core/src/field.rs:390; crates/aspis-core/src/field.rs:1017 | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_ByteFields.lean:47 | `aspis_core.r0.domain.FibreIndex.new` | crates/aspis-core/src/r0/domain.rs:11 (macro instantiated at 24) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.fibre_new | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:50 | `aspis_core.r0.domain.FibreIndex.get` | crates/aspis-core/src/r0/domain.rs:18 (macro instantiated at 24) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.fibre_get | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:51 | `aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq` | crates/aspis-core/src/circle.rs:10 (derived PartialEq) | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:54 | `aspis_core.r0.merkle.C1_TAG` | crates/aspis-core/src/r0/merkle.rs:15 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.c1_tag | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_ByteFields.lean:55 | `aspis_core.r0.merkle.C2_TAG` | crates/aspis-core/src/r0/merkle.rs:16 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.c2_tag | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CheckpointModel.lean:6 | `XRn_Join_asSlice` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CheckpointModel.lean:8 | `XRn_Join_digest` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CheckpointModel.lean:11 | `verifier.checkpoint` | crates/aspis-r1-cost-probe/src/verifier.rs:326 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPm_checkpoint_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_CheckpointModel.lean:38 | `aspis_core.r0.heap.filled` | crates/aspis-core/src/r0/heap.rs:5 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CheckpointModel.lean:41 | `aspis_core.r0.merkle.parent_with_digest` | crates/aspis-core/src/r0/merkle.rs:28 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CheckpointModel.lean:44 | `aspis_core.state_only_private_merkle.private_leaf_hash_with_digest` | crates/aspis-core/src/state_only_private_merkle.rs:40 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_CircleModel.lean:5 | `XRn_Join_qpow` | library model | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_CircleModel.lean:14 | `aspis_core.circle.secure_ood_circle_point_from_parameter` | crates/aspis-core/src/circle.rs:55 | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_CircleModel.lean:28 | `sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once` | crates/aspis-r1-cost-probe/src/sampler.rs:122 (closure; aspis-core transcript fallback) | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_DecodeModels.lean:6 | `r1_wire.ValidatedRecord.decode_k` | crates/aspis-r1-cost-probe/src/r1_wire.rs:139 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.decode_bad_row | Retained LPn_decode_k_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_DecodeModels.lean:32 | `r1_semantic.claims` | crates/aspis-r1-cost-probe/src/r1_semantic.rs:42 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPn_claims_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_DecodeModels.lean:49 | `r1_semantic.semantic_boundary` | crates/aspis-r1-cost-probe/src/r1_semantic.rs:81 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPo_semantic_boundary_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_DecodeModels.lean:55 | `XRn_Join_sliceRange` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DecodeModels.lean:61 | `verifier.candidate.wide_view` | crates/aspis-r1-cost-probe/src/candidate.rs:76 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPo_wide_view_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_DotModel.lean:6 | `XRn_Join_wrap64` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:7 | `XRn_Join_sub64` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:8 | `XRn_Join_partial` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:9 | `XRn_Join_raw` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:21 | `XRn_Join_u64` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:23 | `fast_pairing.canonical.Dot.push` | crates/aspis-r1-cost-probe/src/fast_pairing.rs:114; crates/aspis-r1-cost-probe/src/fast_pairing.rs:165; crates/aspis-r1-cost-probe/src/fast_pairing.rs:203 | NO EMITTED BODY in raw Funs | FAITHFUL | KSA_L031 KSA.dot_native, universal emitted-body result | Retained LPn_Dot_push_LEAF native/Kani scope; no unchanged rerun |
| XRn_Join_DotModel.lean:30 | `XRn_Join_dotFinish` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:33 | `XRn_Join_usize` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:34 | `XRn_Join_toQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:36 | `XRn_Join_dotZero` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:37 | `XRn_Join_powers` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:44 | `XRn_Join_preparedPart` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_DotModel.lean:75 | `verifier.prepared_claim` | crates/aspis-r1-cost-probe/src/verifier.rs:53 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPm_prepared_claim_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_Field.lean:5 | `field.M31` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:6 | `field.CM31` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:7 | `field.QM31` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:11 | `field.P` | crates/aspis-core/src/field.rs:19 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:12 | `field.M31.add` | crates/aspis-core/src/field.rs:62 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.add | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:22 | `field.M31.double` | crates/aspis-core/src/field.rs:183:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:28 | `field.M31.sub` | crates/aspis-core/src/field.rs:94:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:38 | `field.mul_by_r` | crates/aspis-core/src/field.rs:860:0 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:47 | `field.reduce_u64` | crates/aspis-core/src/field.rs:31:0 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:64 | `field.M31.reduce_u64` | crates/aspis-core/src/field.rs:153:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:71 | `field.M31.mul` | crates/aspis-core/src/field.rs:133:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:81 | `field.CM31.mul` | crates/aspis-core/src/field.rs:306:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:105 | `field.CM31.sub` | crates/aspis-core/src/field.rs:289:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:114 | `field.CM31.add` | crates/aspis-core/src/field.rs:281:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:123 | `field.QM31.mul` | crates/aspis-core/src/field.rs:935:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:139 | `field.QM31.sub` | crates/aspis-core/src/field.rs:906:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:148 | `field.QM31.add` | crates/aspis-core/src/field.rs:896:4 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Field.lean:156 | `field.wide_exact.mul_u` | crates/aspis-core/src/field/wide_exact.rs:299:0 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:8 | `oldQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L002 KSA.carrier_roundtrip, universal record roundtrip | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:10 | `newQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L002 KSA.carrier_roundtrip, universal record roundtrip | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:12 | `qzero` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:13 | `qone` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:14 | `qeq` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:17 | `canon` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.canonical | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:28 | `aspis_core.field.P` | crates/aspis-core/src/field.rs:19 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.p | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:29 | `aspis_core.field.M31.ZERO` | crates/aspis-core/src/field.rs:55 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.zero | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:30 | `aspis_core.field.M31.ONE` | crates/aspis-core/src/field.rs:56 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.one | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:31 | `aspis_core.field.M31.Insts.CoreCloneClone.clone` | library model (derived Clone/PartialEq, crates/aspis-core/src/field.rs) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.clone | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:32 | `aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq` | library model (derived Clone/PartialEq, crates/aspis-core/src/field.rs) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.eq | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:33 | `aspis_core.field.M31.sub` | crates/aspis-core/src/field.rs:94; crates/aspis-core/src/field.rs:289; crates/aspis-core/src/field.rs:906 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.sub | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:34 | `aspis_core.field.M31.mul` | crates/aspis-core/src/field.rs:133; crates/aspis-core/src/field.rs:306; crates/aspis-core/src/field.rs:460; crates/aspis-core/src/field.rs:935 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.mul | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:35 | `aspis_core.field.M31.reduce_u64` | crates/aspis-core/src/field.rs:31; crates/aspis-core/src/field.rs:153 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.reduce | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:36 | `aspis_core.field.M31.double` | crates/aspis-core/src/field.rs:183; crates/aspis-core/src/field.rs:346 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.double | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:37 | `aspis_core.field.CM31.new` | crates/aspis-core/src/field.rs:271; crates/aspis-core/src/field.rs:448; crates/aspis-core/src/field.rs:1280 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.cm_new | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:38 | `aspis_core.field.CM31.mul` | crates/aspis-core/src/field.rs:133; crates/aspis-core/src/field.rs:306; crates/aspis-core/src/field.rs:460; crates/aspis-core/src/field.rs:935 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.cm_mul | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:39 | `aspis_core.field.QM31.Insts.CoreCloneClone.clone` | library model (derived Clone/PartialEq, crates/aspis-core/src/field.rs) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_clone | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:40 | `aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne` | library model (derived Clone/PartialEq, crates/aspis-core/src/field.rs) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_ne | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:41 | `aspis_core.field.QM31.ZERO` | crates/aspis-core/src/field.rs:55 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_zero | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:42 | `aspis_core.field.QM31.ONE` | crates/aspis-core/src/field.rs:56 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_one | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:43 | `aspis_core.field.QM31.add` | crates/aspis-core/src/field.rs:62; crates/aspis-core/src/field.rs:281; crates/aspis-core/src/field.rs:896 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_add | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:44 | `aspis_core.field.QM31.mul` | crates/aspis-core/src/field.rs:133; crates/aspis-core/src/field.rs:306; crates/aspis-core/src/field.rs:460; crates/aspis-core/src/field.rs:935 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.q_mul | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:47 | `XRn_Join_Wide` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:48 | `aspis_core.field.wide_exact.WideExact.ZERO` | crates/aspis-core/src/field/wide_exact.rs:41 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_zero | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:49 | `aspis_core.field.wide_exact.WideExact.ONE` | crates/aspis-core/src/field/wide_exact.rs:45 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_one | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:50 | `aspis_core.field.wide_exact.WideExact.new` | crates/aspis-core/src/field/wide_exact.rs:55 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_new | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:54 | `aspis_core.field.wide_exact.WideExact.from_qm31` | crates/aspis-core/src/field/wide_exact.rs:73 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_from | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_FieldExternal.lean:56 | `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.ne` | library model (derived Clone/PartialEq, crates/aspis-core/src/field/wide_exact.rs) | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_ne | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:58 | `aspis_core.field.wide_exact.WideExact.add` | crates/aspis-core/src/field/wide_exact.rs:81 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_add | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_FieldExternal.lean:62 | `aspis_core.field.wide_exact.WideExact.sub` | crates/aspis-core/src/field/wide_exact.rs:91 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_sub | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:68 | `aspis_core.field.wide_exact.WideExact.mul` | crates/aspis-core/src/field/wide_exact.rs:112 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_mul | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FieldExternal.lean:79 | `aspis_core.field.wide_exact.WideExact.mul_qm31` | crates/aspis-core/src/field/wide_exact.rs:178 | NO EMITTED BODY in raw Funs | UNFAITHFUL | KSA_L030 KSA.Small.w_mulq | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_FieldExternal.lean:83 | `aspis_core.field.wide_exact.WideExact.mul_m31` | crates/aspis-core/src/field/wide_exact.rs:190 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L030 KSA.Small.w_mulm | KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam |
| XRn_Join_Funs.lean:54 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT` | /rustc/library/core/src/slice/iter/macros.rs:153:8 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:82 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT` | /rustc/library/core/src/slice/iter/macros.rs:436:8 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:685 | `verifier.candidate.canonical_scan` | crates/aspis-r1-cost-probe/src/candidate.rs:54:0 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:1153 | `multiproof.verify_in_place_loop0_loop0_loop0.body` | crates/aspis-r1-cost-probe/src/multiproof.rs:174:20 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:1993 | `verifier.update_residue_row` | crates/aspis-r1-cost-probe/src/verifier.rs:235:0 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3518 | `sampler.add_small_base_p` | crates/aspis-r1-cost-probe/src/sampler.rs:90:0 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3597 | `sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body` | crates/aspis-r1-cost-probe/src/sampler.rs:61:8 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3649 | `sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut` | crates/aspis-r1-cost-probe/src/sampler.rs:59:38 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3687 | `sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32` | crates/aspis-r1-cost-probe/src/sampler.rs:59:38 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3699 | `sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32` | crates/aspis-r1-cost-probe/src/sampler.rs:59:38 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:3764 | `sampler.low_base_p_digits` | crates/aspis-r1-cost-probe/src/sampler.rs:56:0 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:6050 | `compact.expand_semantic_loop.body` | crates/aspis-r1-cost-probe/src/compact.rs:154:4 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:6235 | `verifier.candidate.prepare` | crates/aspis-r1-cost-probe/src/candidate.rs:255:0 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:6349 | `verifier.BatchedWeights.finish_loop.body` | crates/aspis-r1-cost-probe/src/verifier.rs:226:38 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_Funs.lean:6399 | `verifier.BatchedWeights.finish` | crates/aspis-r1-cost-probe/src/verifier.rs:226:4 | DIFFERENT | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:9 | `core.iter.traits.iterator.Iterator.any.default` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:31 | `core.iter.traits.iterator.Iterator.all.default` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:53 | `core.iter.traits.iterator.Iterator.fold.default` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:72 | `core.array.fromFnList` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:87 | `core.array.from_fn` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:98 | `core.array.mapListFnMut` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:111 | `core.array.Array.map` | crates/aspis-statement/src/state_only_trace.rs:116 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:119 | `MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:127 | `core.option.Option.ok_or` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:133 | `core.slice.iter.Windows.windowAt` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:144 | `core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:154 | `core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:168 | `core.slice.Slice.windows` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:174 | `alloc.vec.Vec.is_empty` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:179 | `Slice.Insts.CoreCmpPartialEqArray.eq` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:186 | `Slice.Insts.CoreCmpPartialEqArray.ne` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:192 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:200 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:208 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:215 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:228 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:246 | `core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:269 | `core.iter.traits.iterator.Iterator.map.default` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:279 | `core.result.Result.unwrap_or_else` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:289 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.any` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:297 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.all` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:305 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.fold` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:313 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.collect` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:321 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:332 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.enumerate` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:340 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.map` | crates/aspis-statement/src/state_only_trace.rs:116 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:349 | `core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.step_by` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:357 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rev` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:368 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:377 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map` | crates/aspis-statement/src/state_only_trace.rs:116 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:386 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.step_by` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:394 | `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.collect` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:402 | `core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:414 | `le32` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:417 | `validChunk` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:422 | `chunksValid` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_FunsExternal.lean:429 | `compact.check_values` | crates/aspis-r1-cost-probe/src/compact.rs:139 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.compact_empty | Retained LPl_check_values_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_FunsExternal.lean:435 | `verifier.echeck` | crates/aspis-r1-cost-probe/src/verifier.rs:39 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.echeck_empty | Retained LPl_echeck_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_FunsExternal.lean:441 | `r1_wire.validate_record_fields` | crates/aspis-r1-cost-probe/src/r1_wire.rs:50 | NO EMITTED BODY in raw Funs | UNDETERMINED | KSA_L038/039 KSA.Bytes.validate_empty | Retained LPl_validate_record_fields_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_FunsExternal.lean:454 | `compact.expand_values` | crates/aspis-r1-cost-probe/src/compact.rs:127 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | Retained LPl_expand_values_LEAF.md native gate, original domain only; no fresh gate or universal association inferred |
| XRn_Join_MaskModel.lean:6 | `XRn_Join_basis` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_MaskModel.lean:12 | `XRn_Join_scaleQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_MaskModel.lean:14 | `aspis_core.state_only_hiding.state_only_selected_mask_value` | crates/aspis-core/src/state_only_hiding.rs:647 | NO EMITTED BODY in raw Funs | UNFAITHFUL | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | KSA_R002, KSA_R004 or KSA_R006 (see failure matrix) |
| XRn_Join_PublicModel.lean:7 | `XRn_Join_oldLive` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_PublicModel.lean:15 | `XRn_Join_oldAfter` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_PublicModel.lean:18 | `XRn_Join_oldTransition` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_PublicModel.lean:21 | `XRn_Join_oldPublic` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_PublicModel.lean:34 | `aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes` | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2017 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_QueryModel.lean:7 | `XRn_Join_scanWord` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_QueryModel.lean:12 | `aspis_core.r0_transcript.queries_from_pairs` | crates/aspis-core/src/r0_transcript.rs:305 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:6 | `XRn_Join_next` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:10 | `XRn_Join_iterator` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:12 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:18 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:23 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:29 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:35 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.map` | crates/aspis-statement/src/state_only_trace.rs:116 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:41 | `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.collect` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:48 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_StdExtra.lean:60 | `core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:8 | `XRn_Join_nativeLive` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:16 | `XRn_Join_nativeAfter` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:19 | `XRn_Join_nativeTransition` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:22 | `XRn_Join_nativePublic` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:35 | `XRn_Join_nativeQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:36 | `XRn_Join_releaseQ` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:37 | `XRn_Join_mapArray` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:39 | `XRn_Join_oldChallenges` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:43 | `XRn_Join_newError` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TerminalModel.lean:49 | `aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31` | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2080 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TypesExternal.lean:6 | `core.slice.iter.Windows` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TypesExternal.lean:13 | `aspis_core.field.wide_exact.WideExact` | crates/aspis-core/src/field/wide_exact.rs:28 | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRn_Join_TypesExternal.lean:18 | `aspis_core.r0.domain.FibreIndex` | library model | NO EMITTED BODY in raw Funs | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:7 | `Q` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:8 | `E` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:9 | `V` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:10 | `Point` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:11 | `Challenges` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:12 | `Sem` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:13 | `ST` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:14 | `T` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:15 | `View` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:16 | `Prepared` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:17 | `D` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:18 | `Err` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:21 | `Q` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:22 | `V` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:23 | `Point` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:24 | `Challenges` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:25 | `Sem` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:26 | `ST` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:27 | `T` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:28 | `View` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:29 | `Prepared` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:30 | `D` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:31 | `Err` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:34 | `arr` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:36 | `cq` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:37 | `eq` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:38 | `cv` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:39 | `ev` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:40 | `cp` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:41 | `ep` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:42 | `cc` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:44 | `ec` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:46 | `cst` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:47 | `est` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:48 | `ct` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:49 | `et` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:50 | `cs` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:53 | `es` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:56 | `cview` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:58 | `eview` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:60 | `cprepared` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:63 | `eprepared` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:66 | `cd` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:67 | `ed` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:68 | `ce` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:72 | `ee` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:77 | `inner` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Carriers.lean:79 | `mapR` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Installed.lean:16 | `actual` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Nonvacuity.lean:7 | `copyUnit` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_Nonvacuity.lean:8 | `failingDigest` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDecode.lean:8 | `q` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:9 | `divBody` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:10 | `divLoop` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:11 | `divPass` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:15 | `divBody` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:16 | `divLoop` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_OrdinaryDigits.lean:17 | `divPass` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PowersLoop.lean:7 | `E` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PowersLoop.lean:8 | `chosen` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PreparedBoundaries.lean:9 | `query` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PreparedBoundaries.lean:11 | `cachedClaim` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PreparedBoundaries.lean:15 | `sampling` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_PreparedBoundaries.lean:25 | `boundaries` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:9 | `divBody` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:10 | `divLoop` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:11 | `divPass` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:12 | `digits0Body` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:13 | `digits0` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:14 | `digits1Body` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:15 | `digits1` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:16 | `digits` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:20 | `divBody` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:21 | `divLoop` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:22 | `divPass` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:23 | `digits0Body` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:24 | `digits0` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:25 | `digits1Body` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:26 | `digits1` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XRo_Join_QmSampler.lean:27 | `digits` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |
| XSd_InverseShape.lean:6 | `spine` | library model | successor adapter, not raw emission | UNDETERMINED | No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED | No fresh differential of this definition; UNDETERMINED |

## Merged theorem dependency lists

### Exact paths to refuted stand-ins

43 explicit merged source theorems in the queried XR environment have a statement/proof path to one of the eight UNFAITHFUL definitions. Paths include statements, so a rejected-branch theorem may mention a whole function without executing its bad branch. Diagnostic refutations are listed too, and remain valid counterexample theorems.

| Theorem | Source | Refuted definition |
|---|---|---|
| `XRn_JoinedGeometry.reversed_range` | evidence/extraction-assoc6-20261027/XRn_JoinedGeometry.lean:40 | `aspis_core.field.M31.inv` |
| `XRr_Accepted64.source` | evidence/extraction-assoc10-20261027/XRr_Accepted64.lean:8 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_AccumulateFrame.weights` | evidence/extraction-assoc10-20261027/XRr_AccumulateFrame.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_Candidate64.source` | evidence/extraction-assoc10-20261027/XRr_Candidate64.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_CandidateCheckpoint.source` | evidence/extraction-assoc10-20261027/XRr_CandidateCheckpoint.lean:8 | `aspis_core.field.M31.inv` |
| `XRr_CandidateCuts.source` | evidence/extraction-assoc10-20261027/XRr_CandidateCuts.lean:7 | `aspis_core.field.M31.inv` |
| `XRr_CandidateEarlierReject.parse_error` | evidence/extraction-assoc10-20261027/XRr_CandidateEarlierReject.lean:5 | `aspis_core.field.M31.inv` |
| `XRr_CandidateEarlierReject.scan_error` | evidence/extraction-assoc10-20261027/XRr_CandidateEarlierReject.lean:20 | `aspis_core.field.M31.inv` |
| `XRr_CandidateReject.wrong_split` | evidence/extraction-assoc10-20261027/XRr_CandidateReject.lean:5 | `aspis_core.field.M31.inv` |
| `XRr_CandidateReject.zero_split` | evidence/extraction-assoc10-20261027/XRr_CandidateReject.lean:14 | `aspis_core.field.M31.inv` |
| `XRr_FinishEarlierReject.rounds_error` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:5 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_FinishEarlierReject.rounds_fail` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:16 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_FinishEarlierReject.rounds_div` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:26 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_Materialized64.source` | evidence/extraction-assoc10-20261027/XRr_Materialized64.lean:9 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_Nonvacuity.emitted_observed` | evidence/extraction-assoc10-20261027/XRr_Nonvacuity.lean:6 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_Nonvacuity.stopped_query` | evidence/extraction-assoc10-20261027/XRr_Nonvacuity.lean:12 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_ObservedCuts.source` | evidence/extraction-assoc10-20261027/XRr_ObservedCuts.lean:7 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedEarlierReject.public_error` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:5 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedEarlierReject.begin_error` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:17 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedEarlierReject.begin_fail` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:31 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedReject.parse_error` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:6 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedReject.parse_fail` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:15 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_ObservedReject.parse_div` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:23 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRr_QueryCalls.source` | evidence/extraction-assoc10-20261027/XRr_QueryCalls.lean:16 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryCalls.weights` | evidence/extraction-assoc10-20261027/XRr_QueryCalls.lean:60 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFailure.fail` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:6 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFailure.div` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:16 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFailure.rejected` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:26 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFailureCuts.index_fail` | evidence/extraction-assoc10-20261027/XRr_QueryFailureCuts.lean:6 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFrame.accumulate` | evidence/extraction-assoc10-20261027/XRr_QueryFrame.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFrame.query` | evidence/extraction-assoc10-20261027/XRr_QueryFrame.lean:30 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryStop.rejected` | evidence/extraction-assoc10-20261027/XRr_QueryStop.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryStop.stopped` | evidence/extraction-assoc10-20261027/XRr_QueryStop.lean:16 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRu_CandidatePending64.source` | evidence/extraction-assoc13-20261027/XRu_CandidatePending64.lean:8 | `aspis_core.field.M31.inv` |
| `XRz_HybridCuts.source` | evidence/extraction-assoc18-20261027/XRz_HybridCuts.lean:8 | `aspis_core.field.M31.inv` |
| `XRz_HybridPrepareRaw.source` | evidence/extraction-assoc18-20261027/XRz_HybridPrepareRaw.lean:6 | `aspis_core.state_only_hiding.state_only_selected_mask_value` |
| `XRz_HybridTx1Raw.source` | evidence/extraction-assoc18-20261027/XRz_HybridTx1Raw.lean:6 | `aspis_core.field.M31.inv` |
| `XSd_InverseCompare.kit_two` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:6 | `aspis_core.field.M31.inv` |
| `XSd_InverseCompare.mismatch` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:22 | `aspis_core.field.M31.inv` |
| `XSd_InverseCompare.both_success` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:29 | `aspis_core.field.M31.inv` |
| `XSd_InverseShape.even` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:10 | `XRn_Join_mpow` |
| `XSd_InverseShape.spine_one` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:26 | `XRn_Join_mpow` |
| `XSd_InverseShape.inverse_spine` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:31 | `XRn_Join_mpow` |

### Exact unresolved paths and conservative import candidates

360 explicit source theorem declarations have kernel dependency paths to kit models in the audited environments. 678 further declarations are conservative import candidates, not proved dependencies. Each full path is in KSA_dependencies.json. No source-to-emission credit is inferred from either set.

| Theorem | Source | First model on kernel path |
|---|---|---|
| `XRn_JoinedGeometry.reversed_range` | evidence/extraction-assoc6-20261027/XRn_JoinedGeometry.lean:40 | `core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect` |
| `XRo_Join_Carriers.cq_eq` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:83 | `XRo_Join_Carriers.C.Q` |
| `XRo_Join_Carriers.eq_cq` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:84 | `XRo_Join_Carriers.E.Q` |
| `XRo_Join_Carriers.cv_ev` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:85 | `XRo_Join_Carriers.ev` |
| `XRo_Join_Carriers.ev_cv` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:86 | `XRo_Join_Carriers.E.V` |
| `XRo_Join_Carriers.cp_ep` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:87 | `XRo_Join_Carriers.ep` |
| `XRo_Join_Carriers.ep_cp` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:88 | `XRo_Join_Carriers.ep` |
| `XRo_Join_Carriers.arr_inverse` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:89 | `XRo_Join_Carriers.arr` |
| `XRo_Join_Carriers.cc_ec` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:95 | `XRo_Join_Carriers.C.Challenges` |
| `XRo_Join_Carriers.ec_cc` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:96 | `XRo_Join_Carriers.ec` |
| `XRo_Join_Carriers.cst_est` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:97 | `XRo_Join_Carriers.est` |
| `XRo_Join_Carriers.est_cst` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:98 | `XRo_Join_Carriers.E.ST` |
| `XRo_Join_Carriers.ct_et` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:99 | `XRo_Join_Carriers.ct` |
| `XRo_Join_Carriers.et_ct` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:100 | `XRo_Join_Carriers.ct` |
| `XRo_Join_Carriers.cs_es` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:101 | `XRo_Join_Carriers.C.Challenges` |
| `XRo_Join_Carriers.es_cs` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:102 | `XRo_Join_Carriers.ec` |
| `XRo_Join_Carriers.cview_eview` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:103 | `aspis_core.field.wide_exact.WideExact` |
| `XRo_Join_Carriers.eview_cview` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:104 | `aspis_core.field.wide_exact.WideExact` |
| `XRo_Join_Carriers.cprepared_eprepared` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:105 | `aspis_core.field.wide_exact.WideExact` |
| `XRo_Join_Carriers.eprepared_cprepared` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:106 | `aspis_core.field.wide_exact.WideExact` |
| `XRo_Join_Carriers.cd_ed` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:107 | `XRo_Join_Carriers.cd` |
| `XRo_Join_Carriers.ed_cd` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:108 | `XRo_Join_Carriers.cd` |
| `XRo_Join_Carriers.ce_ee` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:109 | `XRo_Join_Carriers.C.Err` |
| `XRo_Join_Carriers.ee_ce` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:110 | `XRo_Join_Carriers.ee` |
| `XRo_Join_Carriers.mapR_bind` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:112 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_Carriers.nested_roundtrip` | evidence/extraction-assoc7-20261027/XRo_Join_Carriers.lean:115 | `XRo_Join_Carriers.E.Prepared` |
| `XRo_Join_DivPass.pass` | evidence/extraction-assoc7-20261027/XRo_Join_DivPass.lean:6 | `XRo_Join_OrdinaryDigits.C.divLoop` |
| `XRo_Join_Installed.powers_slot` | evidence/extraction-assoc7-20261027/XRo_Join_Installed.lean:20 | `XRo_Join_Installed.actual` |
| `XRo_Join_Installed.cached_claim_slot` | evidence/extraction-assoc7-20261027/XRo_Join_Installed.lean:21 | `XRo_Join_Installed.actual` |
| `XRo_Join_Installed.serializer_slot` | evidence/extraction-assoc7-20261027/XRo_Join_Installed.lean:22 | `XRo_Join_Installed.actual` |
| `XRo_Join_Installed.start` | evidence/extraction-assoc7-20261027/XRo_Join_Installed.lean:26 | `XRo_Join_Carriers.ct` |
| `XRo_Join_Installed.legacy_claim_unused` | evidence/extraction-assoc7-20261027/XRo_Join_Installed.lean:32 | `XRo_Join_Carriers.C.View` |
| `XRo_Join_OrdinaryDecode.canonical` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDecode.lean:11 | `XRn_Join_FieldExternal.canon` |
| `XRo_Join_OrdinaryDecode.wide_new` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDecode.lean:19 | `XRn_Join_FieldExternal.canon` |
| `XRo_Join_OrdinaryDecode.decode` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDecode.lean:28 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_OrdinaryDecode.ordinary_slot` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDecode.lean:38 | `XRo_Join_Installed.actual` |
| `XRo_Join_OrdinaryDigits.div_body` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDigits.lean:20 | `XRo_Join_OrdinaryDigits.E.divBody` |
| `XRo_Join_OrdinaryDigits.div_loop` | evidence/extraction-assoc7-20261027/XRo_Join_OrdinaryDigits.lean:26 | `XRo_Join_OrdinaryDigits.C.divLoop` |
| `XRo_Join_PreparedBoundaries.legacy_claim_unused` | evidence/extraction-assoc7-20261027/XRo_Join_PreparedBoundaries.lean:32 | `XRo_Join_PreparedBoundaries.sampling` |
| `XRo_Join_PreparedScalars.scalar` | evidence/extraction-assoc7-20261027/XRo_Join_PreparedScalars.lean:8 | `aspis_core.field.wide_exact.WideExact` |
| `XRo_Join_PreparedScalars.scalar_k` | evidence/extraction-assoc7-20261027/XRo_Join_PreparedScalars.lean:27 | `XRo_Join_PreparedBoundaries.sampling` |
| `XRo_Join_QmSampler.div_body` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:30 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.div_loop` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:35 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.div_pass` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:42 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.digits1_body` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:52 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.digits1` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:57 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.digits` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:64 | `aspis_core.field.P` |
| `XRo_Join_QmSampler.sample` | evidence/extraction-assoc7-20261027/XRo_Join_QmSampler.lean:68 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultPair.map_let_pair` | evidence/extraction-assoc7-20261027/XRo_Join_ResultPair.lean:7 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_ok` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:7 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_fail` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:8 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_div` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:9 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_if` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:11 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_pair` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:14 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_flow` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:17 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_inner` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:22 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_comp` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:27 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.bind_map` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:30 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_id` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:33 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_ResultTransport.map_injective` | evidence/extraction-assoc7-20261027/XRo_Join_ResultTransport.lean:35 | `XRo_Join_Carriers.mapR` |
| `XRo_Join_Transcript.tag` | evidence/extraction-assoc7-20261027/XRo_Join_Transcript.lean:8 | `XRo_Join_Carriers.ev` |
| `XRo_Join_Transcript.folds` | evidence/extraction-assoc7-20261027/XRo_Join_Transcript.lean:12 | `XRo_Join_Carriers.ev` |
| `XRo_Join_Transcript.start` | evidence/extraction-assoc7-20261027/XRo_Join_Transcript.lean:16 | `XRo_Join_Carriers.ct` |
| `XRo_Join_TranscriptBlock.absorb` | evidence/extraction-assoc7-20261027/XRo_Join_TranscriptBlock.lean:8 | `XRo_Join_Carriers.ct` |
| `XRo_Join_TranscriptBlock.block` | evidence/extraction-assoc7-20261027/XRo_Join_TranscriptBlock.lean:15 | `XRo_Join_Carriers.ct` |
| `XRp_DivisionWitness.emitted` | evidence/extraction-assoc8-20261027/XRp_DivisionWitness.lean:11 | `XRn_Join_revRestored` |
| `XRp_FromFnConstant.constant` | evidence/extraction-assoc8-20261027/XRp_FromFnConstant.lean:6 | `core.array.fromFnList.match_1` |
| `XRp_FromFnState.indexed_eq` | evidence/extraction-assoc8-20261027/XRp_FromFnState.lean:19 | `core.array.fromFnList.match_1` |
| `XRp_FromFnState.from_fn_state_eq` | evidence/extraction-assoc8-20261027/XRp_FromFnState.lean:49 | `core.array.fromFnList` |
| `XRp_LowSamplerObstruction.emitted_low` | evidence/extraction-assoc8-20261027/XRp_LowSamplerObstruction.lean:9 | `core.array.from_fn` |
| `XRp_LowSamplerObstruction.sampler_commutation_false` | evidence/extraction-assoc8-20261027/XRp_LowSamplerObstruction.lean:28 | `core.array.from_fn` |
| `XRp_LowSamplerObstruction.all_blocks_law_false` | evidence/extraction-assoc8-20261027/XRp_LowSamplerObstruction.lean:36 | `core.array.from_fn` |
| `XRp_PowersComplex.add` | evidence/extraction-assoc8-20261027/XRp_PowersComplex.lean:12 | `XRo_Join_Carriers.mapR` |
| `XRp_PowersQAdd.add` | evidence/extraction-assoc8-20261027/XRp_PowersQAdd.lean:11 | `XRo_Join_Carriers.mapR` |
| `XRp_PowersScalar.add` | evidence/extraction-assoc8-20261027/XRp_PowersScalar.lean:6 | `XRn_Join_Field.field.P` |
| `XRp_PowersScalarSub.source` | evidence/extraction-assoc8-20261027/XRp_PowersScalarSub.lean:28 | `XRn_Join_Field.field.P` |
| `XRp_ReverseBodies.zero` | evidence/extraction-assoc8-20261027/XRp_ReverseBodies.lean:13 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back.match_1` |
| `XRp_ReverseBodies.prime` | evidence/extraction-assoc8-20261027/XRp_ReverseBodies.lean:25 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back.match_1` |
| `XRp_ReverseBodies.empty` | evidence/extraction-assoc8-20261027/XRp_ReverseBodies.lean:38 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back.match_1` |
| `XRp_ReversePass.loop_pass` | evidence/extraction-assoc8-20261027/XRp_ReversePass.lean:18 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back.match_1` |
| `XRp_ReverseStep.restores_P` | evidence/extraction-assoc8-20261027/XRp_ReverseStep.lean:17 | `core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back.match_1` |
| `XRp_SamplerNonvacuity.both_succeed` | evidence/extraction-assoc8-20261027/XRp_SamplerNonvacuity.lean:7 | `core.array.from_fn` |
| `XRp_SamplerRepeated.callback_state` | evidence/extraction-assoc8-20261027/XRp_SamplerRepeated.lean:9 | `XRn_Join_revRestored` |
| `XRp_SamplerRepeated.eight_digits` | evidence/extraction-assoc8-20261027/XRp_SamplerRepeated.lean:17 | `core.array.fromFnList` |
| `XRp_SeedArray.suffix7` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:9 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix6` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:16 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix5` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:36 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix4` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:56 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix3` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:76 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix2` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:96 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix1` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:116 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.suffix0` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:136 | `core.array.fromFnList.match_1` |
| `XRp_SeedArray.list_seed` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:156 | `core.array.fromFnList` |
| `XRp_SeedArray.init` | evidence/extraction-assoc8-20261027/XRp_SeedArray.lean:158 | `core.array.fromFnList` |
| `XRq_ComplexSub.sub` | evidence/extraction-assoc9-20261027/XRq_ComplexSub.lean:9 | `XRn_Join_Field.field.M31.sub` |
| `XRq_FromQm.canon` | evidence/extraction-assoc9-20261027/XRq_FromQm.lean:8 | `XRn_Join_FieldExternal.canon` |
| `XRq_FromQm.source` | evidence/extraction-assoc9-20261027/XRq_FromQm.lean:18 | `XRn_Join_FieldExternal.canon` |
| `XRq_GammaAssociation.gamma` | evidence/extraction-assoc9-20261027/XRq_GammaAssociation.lean:12 | `aspis_core.field.wide_exact.WideExact` |
| `XRq_GammaDecode.decode` | evidence/extraction-assoc9-20261027/XRq_GammaDecode.lean:8 | `XRo_Join_Carriers.mapR` |
| `XRq_GammaScalar.source` | evidence/extraction-assoc9-20261027/XRq_GammaScalar.lean:9 | `XRo_Join_Carriers.ct` |
| `XRq_LeafErrors.ordinary_fail` | evidence/extraction-assoc9-20261027/XRq_LeafErrors.lean:7 | `XRo_Join_Carriers.C.E` |
| `XRq_LeafErrors.ordinary_div` | evidence/extraction-assoc9-20261027/XRq_LeafErrors.lean:10 | `XRo_Join_Carriers.C.E` |
| `XRq_LeafErrors.gamma_fail` | evidence/extraction-assoc9-20261027/XRq_LeafErrors.lean:13 | `XRo_Join_Carriers.C.E` |
| `XRq_LeafErrors.gamma_div` | evidence/extraction-assoc9-20261027/XRq_LeafErrors.lean:16 | `XRo_Join_Carriers.C.E` |
| `XRq_OrdinaryScalar.raw` | evidence/extraction-assoc9-20261027/XRq_OrdinaryScalar.lean:17 | `XRo_Join_Carriers.C.E` |
| `XRq_OrdinaryScalar.ordinary` | evidence/extraction-assoc9-20261027/XRq_OrdinaryScalar.lean:23 | `XRo_Join_Carriers.ct` |
| `XRq_QmSub.sub` | evidence/extraction-assoc9-20261027/XRq_QmSub.lean:9 | `XRn_Join_Field.field.QM31.sub` |
| `XRq_SamplerInterface.raw_ordinary` | evidence/extraction-assoc9-20261027/XRq_SamplerInterface.lean:24 | `XRo_Join_Carriers.C.E` |
| `XRq_SamplerInterface.raw_gamma` | evidence/extraction-assoc9-20261027/XRq_SamplerInterface.lean:28 | `XRo_Join_Carriers.C.E` |
| `XRq_SamplerInterface.ordinary_cohort` | evidence/extraction-assoc9-20261027/XRq_SamplerInterface.lean:34 | `aspis_core.field.wide_exact.WideExact` |
| `XRq_SamplerInterface.ordinary_native` | evidence/extraction-assoc9-20261027/XRq_SamplerInterface.lean:48 | `aspis_core.field.wide_exact.WideExact` |
| `XRq_ScalarK.source` | evidence/extraction-assoc9-20261027/XRq_ScalarK.lean:7 | `XRo_Join_Carriers.ct` |
| `XRq_ScalarSub.sub` | evidence/extraction-assoc9-20261027/XRq_ScalarSub.lean:8 | `XRn_Join_Field.field.M31.sub` |
| `XRr_Accepted64.source` | evidence/extraction-assoc10-20261027/XRr_Accepted64.lean:8 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_AccumulateFrame.weights` | evidence/extraction-assoc10-20261027/XRr_AccumulateFrame.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_Candidate64.source` | evidence/extraction-assoc10-20261027/XRr_Candidate64.lean:7 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CandidateCheckpoint.source` | evidence/extraction-assoc10-20261027/XRr_CandidateCheckpoint.lean:8 | `XRn_Join_digest` |
| `XRr_CandidateCuts.source` | evidence/extraction-assoc10-20261027/XRr_CandidateCuts.lean:7 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CandidateEarlierReject.parse_error` | evidence/extraction-assoc10-20261027/XRr_CandidateEarlierReject.lean:5 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CandidateEarlierReject.scan_error` | evidence/extraction-assoc10-20261027/XRr_CandidateEarlierReject.lean:20 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CandidateReject.wrong_split` | evidence/extraction-assoc10-20261027/XRr_CandidateReject.lean:5 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CandidateReject.zero_split` | evidence/extraction-assoc10-20261027/XRr_CandidateReject.lean:14 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_CheckpointAttempts.source` | evidence/extraction-assoc10-20261027/XRr_CheckpointAttempts.lean:10 | `XRn_Join_asSlice` |
| `XRr_CheckpointFinalize.value` | evidence/extraction-assoc10-20261027/XRr_CheckpointFinalize.lean:8 | `XRn_Join_asSlice` |
| `XRr_CheckpointFinalize.length` | evidence/extraction-assoc10-20261027/XRr_CheckpointFinalize.lean:14 | `XRn_Join_asSlice` |
| `XRr_CheckpointLayout.slice` | evidence/extraction-assoc10-20261027/XRr_CheckpointLayout.lean:24 | `XRn_Join_asSlice` |
| `XRr_CheckpointReject.first_fail` | evidence/extraction-assoc10-20261027/XRr_CheckpointReject.lean:5 | `XRn_Join_asSlice` |
| `XRr_CheckpointReject.first_div` | evidence/extraction-assoc10-20261027/XRr_CheckpointReject.lean:12 | `XRn_Join_asSlice` |
| `XRr_CheckpointReject.second_fail` | evidence/extraction-assoc10-20261027/XRr_CheckpointReject.lean:19 | `XRn_Join_asSlice` |
| `XRr_CheckpointShape.slice` | evidence/extraction-assoc10-20261027/XRr_CheckpointShape.lean:7 | `XRn_Join_asSlice` |
| `XRr_CheckpointShape.size` | evidence/extraction-assoc10-20261027/XRr_CheckpointShape.lean:14 | `XRn_Join_asSlice` |
| `XRr_EmptySemantic.emitted` | evidence/extraction-assoc10-20261027/XRr_EmptySemantic.lean:9 | `core.option.Option.ok_or` |
| `XRr_EnumerateFrame.source` | evidence/extraction-assoc10-20261027/XRr_EnumerateFrame.lean:6 | `XRn_Join_enumerateNext` |
| `XRr_FinishEarlierReject.rounds_error` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:5 | `aspis_core.field.QM31.add` |
| `XRr_FinishEarlierReject.rounds_fail` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:16 | `aspis_core.field.QM31.add` |
| `XRr_FinishEarlierReject.rounds_div` | evidence/extraction-assoc10-20261027/XRr_FinishEarlierReject.lean:26 | `aspis_core.field.QM31.add` |
| `XRr_FinishLength.loop` | evidence/extraction-assoc10-20261027/XRr_FinishLength.lean:7 | `XRn_Join_enumerateNext` |
| `XRr_FinishLength.source` | evidence/extraction-assoc10-20261027/XRr_FinishLength.lean:20 | `XRn_Join_enumerateRestored` |
| `XRr_FinishStep.source` | evidence/extraction-assoc10-20261027/XRr_FinishStep.lean:10 | `XRn_Join_enumerateNext` |
| `XRr_Initial64.filled` | evidence/extraction-assoc10-20261027/XRr_Initial64.lean:29 | `aspis_core.r0.heap.filled` |
| `XRr_Initial64.init` | evidence/extraction-assoc10-20261027/XRr_Initial64.lean:38 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRr_Materialized64.source` | evidence/extraction-assoc10-20261027/XRr_Materialized64.lean:9 | `verifier.checkpoint` |
| `XRr_Nonvacuity.emitted_observed` | evidence/extraction-assoc10-20261027/XRr_Nonvacuity.lean:6 | `aspis_core.field.QM31.add` |
| `XRr_Nonvacuity.stopped_query` | evidence/extraction-assoc10-20261027/XRr_Nonvacuity.lean:12 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_ObservedCuts.source` | evidence/extraction-assoc10-20261027/XRr_ObservedCuts.lean:7 | `aspis_core.field.QM31.add` |
| `XRr_ObservedEarlierReject.public_error` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:5 | `aspis_core.field.QM31.add` |
| `XRr_ObservedEarlierReject.begin_error` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:17 | `aspis_core.field.QM31.add` |
| `XRr_ObservedEarlierReject.begin_fail` | evidence/extraction-assoc10-20261027/XRr_ObservedEarlierReject.lean:31 | `aspis_core.field.QM31.add` |
| `XRr_ObservedReject.parse_error` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:6 | `aspis_core.field.QM31.add` |
| `XRr_ObservedReject.parse_fail` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:15 | `aspis_core.field.QM31.add` |
| `XRr_ObservedReject.parse_div` | evidence/extraction-assoc10-20261027/XRr_ObservedReject.lean:23 | `aspis_core.field.QM31.add` |
| `XRr_PushExact.returned` | evidence/extraction-assoc10-20261027/XRr_PushExact.lean:7 | `XRn_Join_intoIter` |
| `XRr_PushFrame.terms` | evidence/extraction-assoc10-20261027/XRr_PushFrame.lean:8 | `XRn_Join_intoIter` |
| `XRr_QueryCalls.source` | evidence/extraction-assoc10-20261027/XRr_QueryCalls.lean:16 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryCalls.weights` | evidence/extraction-assoc10-20261027/XRr_QueryCalls.lean:60 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryFailure.fail` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:6 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryFailure.div` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:16 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryFailure.rejected` | evidence/extraction-assoc10-20261027/XRr_QueryFailure.lean:26 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryFailureCuts.index_fail` | evidence/extraction-assoc10-20261027/XRr_QueryFailureCuts.lean:6 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryFrame.accumulate` | evidence/extraction-assoc10-20261027/XRr_QueryFrame.lean:7 | `aspis_core.field.wide_exact.WideExact.mul_qm31` |
| `XRr_QueryFrame.query` | evidence/extraction-assoc10-20261027/XRr_QueryFrame.lean:30 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryStop.rejected` | evidence/extraction-assoc10-20261027/XRr_QueryStop.lean:7 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_QueryStop.stopped` | evidence/extraction-assoc10-20261027/XRr_QueryStop.lean:16 | `aspis_core.field.wide_exact.WideExact` |
| `XRr_RecordAssociation.source` | evidence/extraction-assoc10-20261027/XRr_RecordAssociation.lean:7 | `XRo_Join_Carriers.inner` |
| `XRr_RecordAssociation.validated` | evidence/extraction-assoc10-20261027/XRr_RecordAssociation.lean:17 | `XRo_Join_Carriers.inner` |
| `XRr_SemanticBlock.source` | evidence/extraction-assoc10-20261027/XRr_SemanticBlock.lean:9 | `XRo_Join_Carriers.ed` |
| `XRr_SemanticSample.source` | evidence/extraction-assoc10-20261027/XRr_SemanticSample.lean:7 | `XRo_Join_Carriers.E.Q` |
| `XRs_AddAssociation.add` | evidence/extraction-assoc11-20261027/XRs_AddAssociation.lean:12 | `XRn_Join_intoIter` |
| `XRs_AddLoop.join` | evidence/extraction-assoc11-20261027/XRs_AddLoop.lean:25 | `aspis_core.field.P` |
| `XRs_AddStep.emitted` | evidence/extraction-assoc11-20261027/XRs_AddStep.lean:23 | `aspis_core.field.P` |
| `XRs_AddStep.exhausted` | evidence/extraction-assoc11-20261027/XRs_AddStep.lean:37 | `aspis_core.field.P` |
| `XRs_BaseMultiply.same_reducer` | evidence/extraction-assoc11-20261027/XRs_BaseMultiply.lean:8 | `XRn_Join_Field.field.P` |
| `XRs_BaseMultiply.same_multiply` | evidence/extraction-assoc11-20261027/XRs_BaseMultiply.lean:14 | `XRn_Join_Field.field.M31.mul` |
| `XRs_BaseMultiply.value` | evidence/extraction-assoc11-20261027/XRs_BaseMultiply.lean:19 | `XRn_Join_Field.field.M31.mul` |
| `XRs_BaseMultiply.semantic` | evidence/extraction-assoc11-20261027/XRs_BaseMultiply.lean:25 | `XRn_Join_Field.field.M31.mul` |
| `XRs_ClosedCallbacks.add` | evidence/extraction-assoc11-20261027/XRs_ClosedCallbacks.lean:10 | `XRn_Join_intoIter` |
| `XRs_ClosedCallbacks.scalar` | evidence/extraction-assoc11-20261027/XRs_ClosedCallbacks.lean:12 | `XRo_Join_Carriers.ct` |
| `XRs_ClosedCallbacks.serializer` | evidence/extraction-assoc11-20261027/XRs_ClosedCallbacks.lean:25 | `aspis_core.field.wide_exact.WideExact.to_le_bytes` |
| `XRs_QueryScan.stopped` | evidence/extraction-assoc11-20261027/XRs_QueryScan.lean:18 | `XRn_Join_scanWord` |
| `XRs_QueryScan.scan` | evidence/extraction-assoc11-20261027/XRs_QueryScan.lean:24 | `XRn_Join_scanWord` |
| `XRs_Serializer.same_eight_limbs` | evidence/extraction-assoc11-20261027/XRs_Serializer.lean:8 | `XRn_Join_FieldExternal.newQ` |
| `XRs_WordBytes.word` | evidence/extraction-assoc11-20261027/XRs_WordBytes.lean:10 | `XRn_Join_wordBytes` |
| `XRt_CohortMultiply.multiply` | evidence/extraction-assoc12-20261027/XRt_CohortMultiply.lean:9 | `XRn_Join_Field.field.M31.mul` |
| `XRt_CohortMultiply.canonical_output` | evidence/extraction-assoc12-20261027/XRt_CohortMultiply.lean:17 | `XRn_Join_Field.field.M31.mul` |
| `XRt_QueryScan.same_scan` | evidence/extraction-assoc12-20261027/XRt_QueryScan.lean:8 | `XRn_Join_scanWord` |
| `XRt_QueryScan.same_default` | evidence/extraction-assoc12-20261027/XRt_QueryScan.lean:19 | `XRn_Join_scanWord` |
| `XRt_QueryWord.four` | evidence/extraction-assoc12-20261027/XRt_QueryWord.lean:8 | `XRn_Join_word` |
| `XRt_QueryWord.block_word` | evidence/extraction-assoc12-20261027/XRt_QueryWord.lean:29 | `XRn_Join_word` |
| `XRt_QueryWords.same_words` | evidence/extraction-assoc12-20261027/XRt_QueryWords.lean:11 | `XRn_Join_word` |
| `XRu_CandidatePending64.source` | evidence/extraction-assoc13-20261027/XRu_CandidatePending64.lean:8 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRu_CheckpointTail.source` | evidence/extraction-assoc13-20261027/XRu_CheckpointTail.lean:10 | `XRn_Join_asSlice` |
| `XRu_CheckpointThirdReject.fail` | evidence/extraction-assoc13-20261027/XRu_CheckpointThirdReject.lean:5 | `XRn_Join_asSlice` |
| `XRu_CheckpointThirdReject.div` | evidence/extraction-assoc13-20261027/XRu_CheckpointThirdReject.lean:17 | `XRn_Join_asSlice` |
| `XRu_NewLength.source` | evidence/extraction-assoc13-20261027/XRu_NewLength.lean:18 | `aspis_core.r0.heap.filled` |
| `XRu_PushTransport.source` | evidence/extraction-assoc13-20261027/XRu_PushTransport.lean:14 | `XRo_Join_Carriers.mapR` |
| `XRu_RecordCuts.source` | evidence/extraction-assoc13-20261027/XRu_RecordCuts.lean:8 | `core.option.Option.ok_or` |
| `XRu_RowBoth.source` | evidence/extraction-assoc13-20261027/XRu_RowBoth.lean:20 | `XRn_Join_intoIter` |
| `XRu_RowFoldRun.restore` | evidence/extraction-assoc13-20261027/XRu_RowFoldRun.lean:23 | `XRn_Join_intoIter` |
| `XRu_RowNoFlush.source` | evidence/extraction-assoc13-20261027/XRu_RowNoFlush.lean:8 | `XRn_Join_intoIter` |
| `XRu_RowNonvacuity.total` | evidence/extraction-assoc13-20261027/XRu_RowNonvacuity.lean:7 | `XRn_Join_intoIter` |
| `XRv_DecodedWords.exact_result` | evidence/extraction-assoc14-20261027/XRv_DecodedWords.lean:10 | `XRn_Join_word` |
| `XRv_DecodedWords.continuation` | evidence/extraction-assoc14-20261027/XRv_DecodedWords.lean:17 | `XRn_Join_word` |
| `XRv_DecodedWords.no_failure` | evidence/extraction-assoc14-20261027/XRv_DecodedWords.lean:21 | `XRn_Join_word` |
| `XRv_DecodedWords.no_divergence` | evidence/extraction-assoc14-20261027/XRv_DecodedWords.lean:25 | `XRn_Join_word` |
| `XRv_DriverSelected.selected` | evidence/extraction-assoc14-20261027/XRv_DriverSelected.lean:8 | `XRn_Join_usize` |
| `XRv_QueryDriver.stopped` | evidence/extraction-assoc14-20261027/XRv_QueryDriver.lean:19 | `XRn_Join_usize` |
| `XRv_QueryDriver.short_circuit` | evidence/extraction-assoc14-20261027/XRv_QueryDriver.lean:35 | `XRn_Join_usize` |
| `XRv_QueryDriver.driver` | evidence/extraction-assoc14-20261027/XRv_QueryDriver.lean:54 | `aspis_core.r0_transcript.queries_from_pairs` |
| `XRv_QueryDriverTotal.index` | evidence/extraction-assoc14-20261027/XRv_QueryDriverTotal.lean:8 | `XRn_Join_usize` |
| `XRv_QueryDriverTotal.step_total` | evidence/extraction-assoc14-20261027/XRv_QueryDriverTotal.lean:21 | `XRn_Join_word` |
| `XRv_QueryDriverTotal.fold_total` | evidence/extraction-assoc14-20261027/XRv_QueryDriverTotal.lean:31 | `XRn_Join_word` |
| `XRv_QueryDriverTotal.total` | evidence/extraction-assoc14-20261027/XRv_QueryDriverTotal.lean:43 | `XRn_Join_usize` |
| `XRv_QueryScanTotal.same_block` | evidence/extraction-assoc14-20261027/XRv_QueryScanTotal.lean:29 | `XRn_Join_scanWord` |
| `XRv_SelectedAdvance.step_selected` | evidence/extraction-assoc14-20261027/XRv_SelectedAdvance.lean:8 | `XRn_Join_word` |
| `XRv_SelectedAdvance.fold_selected` | evidence/extraction-assoc14-20261027/XRv_SelectedAdvance.lean:29 | `XRn_Join_usize` |
| `XRw_PairedStep.same_step` | evidence/extraction-assoc15-20261027/XRw_PairedStep.lean:12 | `XRn_Join_usize` |
| `XRx_CheckpointSecondDiv.source` | evidence/extraction-assoc16-20261027/XRx_CheckpointSecondDiv.lean:7 | `XRn_Join_asSlice` |
| `XRx_FinishRaw.value` | evidence/extraction-assoc16-20261027/XRx_FinishRaw.lean:6 | `aspis_core.field.M31.reduce_u64` |
| `XRx_FinishRaw.body` | evidence/extraction-assoc16-20261027/XRx_FinishRaw.lean:10 | `XRn_Join_enumerateNext` |
| `XRx_FinishRaw.loop` | evidence/extraction-assoc16-20261027/XRx_FinishRaw.lean:17 | `XRn_Join_enumerateNext` |
| `XRx_FinishRaw.source` | evidence/extraction-assoc16-20261027/XRx_FinishRaw.lean:23 | `XRn_Join_enumerateRestored` |
| `XRx_FinishStep.source` | evidence/extraction-assoc16-20261027/XRx_FinishStep.lean:11 | `XRo_Join_Carriers.mapR` |
| `XRx_ListMap.source` | evidence/extraction-assoc16-20261027/XRx_ListMap.lean:7 | `core.array.mapListFnMut` |
| `XRx_RecordHeader.source` | evidence/extraction-assoc16-20261027/XRx_RecordHeader.lean:9 | `core.option.Option.ok_or` |
| `XRx_RecordPayload.source` | evidence/extraction-assoc16-20261027/XRx_RecordPayload.lean:7 | `core.option.Option.ok_or` |
| `XRx_ValueNonvacuity.source` | evidence/extraction-assoc16-20261027/XRx_ValueNonvacuity.lean:7 | `XRo_Join_Carriers.mapR` |
| `XRx_ValueOwned.scalar` | evidence/extraction-assoc16-20261027/XRx_ValueOwned.lean:10 | `aspis_core.field.M31.reduce_u64` |
| `XRx_ValueOwned.source` | evidence/extraction-assoc16-20261027/XRx_ValueOwned.lean:19 | `aspis_core.field.M31.reduce_u64` |
| `XRx_ValueRow.map` | evidence/extraction-assoc16-20261027/XRx_ValueRow.lean:8 | `aspis_core.field.M31.reduce_u64` |
| `XRx_ValueRow.source` | evidence/extraction-assoc16-20261027/XRx_ValueRow.lean:29 | `aspis_core.field.M31.reduce_u64` |
| `XRx_ValueScalar.body` | evidence/extraction-assoc16-20261027/XRx_ValueScalar.lean:8 | `aspis_core.field.M31.reduce_u64` |
| `XRx_ValueScalar.source` | evidence/extraction-assoc16-20261027/XRx_ValueScalar.lean:19 | `aspis_core.field.M31.reduce_u64` |
| `XRz_FinishBody.active` | evidence/extraction-assoc18-20261027/XRz_FinishBody.lean:8 | `XRn_Join_enumerateNext` |
| `XRz_FinishBody.stopped` | evidence/extraction-assoc18-20261027/XRz_FinishBody.lean:40 | `XRn_Join_enumerateNext` |
| `XRz_FinishCarrier.source` | evidence/extraction-assoc18-20261027/XRz_FinishCarrier.lean:9 | `XRo_Join_Carriers.mapR` |
| `XRz_FinishLoop.source` | evidence/extraction-assoc18-20261027/XRz_FinishLoop.lean:10 | `aspis_core.field.M31.reduce_u64` |
| `XRz_FinishMaterialize.source` | evidence/extraction-assoc18-20261027/XRz_FinishMaterialize.lean:12 | `XRn_Join_enumerateRestored` |
| `XRz_FinishOwned.source` | evidence/extraction-assoc18-20261027/XRz_FinishOwned.lean:11 | `XRo_Join_Carriers.mapR` |
| `XRz_FinishValue.source` | evidence/extraction-assoc18-20261027/XRz_FinishValue.lean:8 | `XRo_Join_Carriers.mapR` |
| `XRz_HybridCuts.source` | evidence/extraction-assoc18-20261027/XRz_HybridCuts.lean:8 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRz_HybridPrepareRaw.source` | evidence/extraction-assoc18-20261027/XRz_HybridPrepareRaw.lean:6 | `aspis_core.field.wide_exact.WideExact` |
| `XRz_HybridPreparedRaw.source` | evidence/extraction-assoc18-20261027/XRz_HybridPreparedRaw.lean:6 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRz_HybridSampler.ordinary` | evidence/extraction-assoc18-20261027/XRz_HybridSampler.lean:11 | `XRo_Join_Carriers.ct` |
| `XRz_HybridSampler.gamma` | evidence/extraction-assoc18-20261027/XRz_HybridSampler.lean:16 | `XRo_Join_Carriers.ct` |
| `XRz_HybridTx1Raw.source` | evidence/extraction-assoc18-20261027/XRz_HybridTx1Raw.lean:6 | `aspis_core.field.wide_exact.WideExact.ZERO` |
| `XRz_ParseAdvance.source` | evidence/extraction-assoc18-20261027/XRz_ParseAdvance.lean:7 | `core.option.Option.ok_or` |
| `XRz_PushCanonical.source` | evidence/extraction-assoc18-20261027/XRz_PushCanonical.lean:8 | `XRo_Join_Carriers.mapR` |
| `XRz_PushReach.source` | evidence/extraction-assoc18-20261027/XRz_PushReach.lean:16 | `XRo_Join_Carriers.mapR` |
| `XRz_RecordAt.source` | evidence/extraction-assoc18-20261027/XRz_RecordAt.lean:6 | `core.option.Option.ok_or` |
| `XRz_RecordTransport.source` | evidence/extraction-assoc18-20261027/XRz_RecordTransport.lean:9 | `core.option.Option.ok_or` |
| `XRz_RoundDriver.source` | evidence/extraction-assoc18-20261027/XRz_RoundDriver.lean:32 | `aspis_core.field.QM31.ZERO` |
| `XSd_ArrayMap.source` | evidence/extraction-assoc22-20261027/XSd_ArrayMap.lean:8 | `core.array.mapListFnMut` |
| `XSd_DotFinish.four_words` | evidence/extraction-assoc22-20261027/XSd_DotFinish.lean:9 | `core.array.Array.map` |
| `XSd_DotFinishAll.source` | evidence/extraction-assoc22-20261027/XSd_DotFinishAll.lean:8 | `core.array.Array.map` |
| `XSd_DotSequence.sequence` | evidence/extraction-assoc22-20261027/XSd_DotSequence.lean:8 | `core.array.mapListFnMut` |
| `XSd_DotSequence.four` | evidence/extraction-assoc22-20261027/XSd_DotSequence.lean:21 | `core.array.mapListFnMut` |
| `XSd_InverseCompare.kit_two` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:6 | `aspis_core.field.M31.inv` |
| `XSd_InverseCompare.mismatch` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:22 | `aspis_core.field.M31.inv` |
| `XSd_InverseCompare.both_success` | evidence/extraction-assoc22-20261027/XSd_InverseCompare.lean:29 | `aspis_core.field.M31.inv` |
| `XSd_InverseShape.even` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:10 | `aspis_core.field.M31.mul` |
| `XSd_InverseShape.one_mul` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:23 | `aspis_core.field.M31.mul` |
| `XSd_InverseShape.spine_one` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:26 | `aspis_core.field.M31.mul` |
| `XSd_InverseShape.inverse_spine` | evidence/extraction-assoc22-20261027/XSd_InverseShape.lean:31 | `aspis_core.field.M31.inv` |
| `XSd_MapState.source` | evidence/extraction-assoc22-20261027/XSd_MapState.lean:7 | `core.array.mapListFnMut` |
| `LPl_A.Check.loop_eq_model` | evidence/leaf-p6-10-20261027/LPl_A_Check.lean:13 | `LPl_Kit_Bytes.chunksValid` |
| `LPl_A.Check.shipped_leaf_model` | evidence/leaf-p6-10-20261027/LPl_A_Check.lean:17 | `compact.check_values` |
| `LPl_A.Check.loop_eq_fold` | evidence/leaf-p6-10-20261027/LPl_A_Check.lean:22 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Check.accepts_iff` | evidence/leaf-p6-10-20261027/LPl_A_CheckLaws.lean:8 | `compact.check_values` |
| `LPl_A.Check.rejects_of_bad_stage` | evidence/leaf-p6-10-20261027/LPl_A_CheckLaws.lean:15 | `compact.check_values` |
| `LPl_A.Echeck.loop_eq_model` | evidence/leaf-p6-10-20261027/LPl_A_Echeck.lean:12 | `LPl_Kit_Bytes.chunksValid` |
| `LPl_A.Echeck.shipped_leaf_model` | evidence/leaf-p6-10-20261027/LPl_A_Echeck.lean:15 | `verifier.echeck` |
| `LPl_A.Echeck.loop_eq_fold` | evidence/leaf-p6-10-20261027/LPl_A_Echeck.lean:19 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Echeck.accepts_iff` | evidence/leaf-p6-10-20261027/LPl_A_EcheckLaws.lean:8 | `verifier.echeck` |
| `LPl_A.Echeck.rejects_of_bad_stage` | evidence/leaf-p6-10-20261027/LPl_A_EcheckLaws.lean:15 | `verifier.echeck` |
| `LPl_A.Expand.shipped_leaf_model` | evidence/leaf-p6-10-20261027/LPl_A_Expand.lean:16 | `LPl_Kit_Release.compact.CodecError.Length` |
| `LPl_A.check_stage_congruence` | evidence/leaf-p6-10-20261027/LPl_A_ScanCongruence.lean:7 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.echeck_stage_congruence` | evidence/leaf-p6-10-20261027/LPl_A_ScanCongruence.lean:17 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Validate.loop_eq_model` | evidence/leaf-p6-10-20261027/LPl_A_Validate.lean:11 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Validate.loop_eq_fold` | evidence/leaf-p6-10-20261027/LPl_A_Validate.lean:14 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Validate.shipped_leaf_model` | evidence/leaf-p6-10-20261027/LPl_A_Validate.lean:20 | `r1_wire.validate_record_fields` |
| `LPl_A.Validate.error_index_bound` | evidence/leaf-p6-10-20261027/LPl_A_ValidateLaws.lean:8 | `LPl_Kit_Bytes.validChunk` |
| `LPl_A.Validate.error_exact` | evidence/leaf-p6-10-20261027/LPl_A_ValidateLaws.lean:14 | `r1_wire.validate_record_fields` |
| `LPl_A.Validate.accepts_of_all_stages` | evidence/leaf-p6-10-20261027/LPl_A_ValidateLaws.lean:20 | `r1_wire.validate_record_fields` |
| `LPl_C.Echeck.caller_iff` | evidence/leaf-p6-10-20261027/LPl_C_CallerBounds.lean:7 | `verifier.echeck` |
| `LPl_C.Check.caller_iff` | evidence/leaf-p6-10-20261027/LPl_C_CallerBounds.lean:23 | `compact.check_values` |
| `LPl_C.Check.caller_reject` | evidence/leaf-p6-10-20261027/LPl_C_CallerBounds.lean:28 | `compact.check_values` |
| `LPl_C.Validate.caller_success` | evidence/leaf-p6-10-20261027/LPl_C_CallerBounds.lean:37 | `r1_wire.validate_record_fields` |
| `LPl_C.Validate.caller_error_bound` | evidence/leaf-p6-10-20261027/LPl_C_CallerBounds.lean:42 | `LPl_Kit_Bytes.validChunk` |
| `LPl_C.Echeck.append_tail` | evidence/leaf-p6-10-20261027/LPl_C_TailTransport.lean:7 | `LPl_Kit_Bytes.validChunk` |
| `LPl.Check.chunk_eq` | evidence/leaf-p6-10-20261027/LPl_Check.lean:9 | `LPl_Kit_Bytes.le32` |
| `LPl.Check.window` | evidence/leaf-p6-10-20261027/LPl_Check.lean:14 | `LPl_Kit_Bytes.validChunk` |
| `LPl.Check.stage` | evidence/leaf-p6-10-20261027/LPl_Check.lean:19 | `LPl_Kit_Bytes.validChunk` |
| `LPl.Check.native_result` | evidence/leaf-p6-10-20261027/LPl_Check.lean:24 | `compact.check_values` |
| `LPl.Echeck.word_eq_le32` | evidence/leaf-p6-10-20261027/LPl_EcheckBytes.lean:16 | `LPl_Kit_Bytes.le32` |
| `LPl.Echeck.chunk_eq` | evidence/leaf-p6-10-20261027/LPl_EcheckBytes.lean:26 | `LPl_Kit_Bytes.le32` |
| `LPl.Echeck.window` | evidence/leaf-p6-10-20261027/LPl_EcheckBytes.lean:31 | `LPl_Kit_Bytes.validChunk` |
| `LPl.Echeck.run_all` | evidence/leaf-p6-10-20261027/LPl_EcheckResult.lean:6 | `LPl_Kit_Bytes.validChunk` |
| `LPl.Echeck.run_loop` | evidence/leaf-p6-10-20261027/LPl_EcheckResult.lean:19 | `LPl_Kit_Bytes.chunksValid` |
| `LPl.Echeck.native_result` | evidence/leaf-p6-10-20261027/LPl_EcheckResult.lean:27 | `verifier.echeck` |
| `LPl.Expand.native_result` | evidence/leaf-p6-10-20261027/LPl_ExpandResult.lean:14 | `LPl_Kit_Release.compact.CodecError.Length` |
| `LPl.Expand.length_error` | evidence/leaf-p6-10-20261027/LPl_ExpandResult.lean:31 | `LPl_Kit_Release.compact.CodecError.Length` |
| `LPl_G.echeck_stages` | evidence/leaf-p6-10-20261027/LPl_G_Scanners.lean:6 | `LPl_Kit_Bytes.validChunk` |
| `LPl_G.check_stages` | evidence/leaf-p6-10-20261027/LPl_G_Scanners.lean:14 | `LPl_Kit_Bytes.validChunk` |
| `LPn.Bytes.le32_eq_decode` | evidence/leaf-p6-12-20261027/LPn_ByteBound.lean:16 | `LPl_Kit_Bytes.le32` |
| `LPn.Bytes.le32_bound` | evidence/leaf-p6-12-20261027/LPn_ByteBound.lean:18 | `LPl_Kit_Bytes.le32` |
| `LPn.ClaimsModel.fromRecord_spec` | evidence/leaf-p6-12-20261027/LPn_ClaimsFold.lean:17 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.ClaimsModel.leaf_eq_loop` | evidence/leaf-p6-12-20261027/LPn_ClaimsFold.lean:57 | `LPl_Kit_Release.r1_wire.ValidatedRecord.mk` |
| `LPn.ClaimsModel.loop_eq_fold` | evidence/leaf-p6-12-20261027/LPn_ClaimsModel.lean:23 | `LPl_Kit_Release.r1_wire.ValidatedRecord` |
| `LPn.ClaimsModel.leaf_call_order` | evidence/leaf-p6-12-20261027/LPn_ClaimsModel.lean:29 | `LPl_Kit_Release.r1_wire.ValidatedRecord.mk` |
| `LPn.Claims.bound25` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:7 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.read25` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:15 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.native_result` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:21 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.native_success` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:26 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.native_error` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:35 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.allocation_rejection` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:42 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.point_domain` | evidence/leaf-p6-12-20261027/LPn_ClaimsPrefix.lean:45 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Claims.decode_total` | evidence/leaf-p6-12-20261027/LPn_ClaimsTotal.lean:7 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Claims.offset_value` | evidence/leaf-p6-12-20261027/LPn_ClaimsTotal.lean:25 | `LPn_Kit_usize` |
| `LPn.Claims.point_ready` | evidence/leaf-p6-12-20261027/LPn_ClaimsTotal.lean:32 | `LPl_Kit_Release.r1_wire.ValidatedRecord.framed` |
| `LPn.Claims.total` | evidence/leaf-p6-12-20261027/LPn_ClaimsTotal.lean:48 | `LPl_Kit_Release.r1_wire.ValidatedRecord.framed` |
| `LPn.Claims.step_eq` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:19 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.Claims.stages_eq` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:31 | `LPl_Kit_Release.r1_wire.ValidatedRecord` |
| `LPn.Claims.success_length` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:40 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.Claims.from_record` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:54 | `LPl_Kit_Release.r1_wire.ValidatedRecord` |
| `LPn.Claims.prefix_result` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:61 | `LPl_Kit_Release.r1_wire.ValidatedRecord.mk` |
| `LPn.Claims.allocated_result` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:75 | `LPl_Kit_Release.r1_wire.ValidatedRecord.mk` |
| `LPn.Claims.accepted_to_cohort` | evidence/leaf-p6-12-20261027/LPn_ClaimsTrace.lean:83 | `LPl_Kit_Release.r1_wire.Prefix` |
| `LPn.Decode.error_bound` | evidence/leaf-p6-12-20261027/LPn_DecodeBounds.lean:6 | `LPl_Kit_Release.r1_wire.ValidatedRecord.framed` |
| `LPn.Decode.token_unique` | evidence/leaf-p6-12-20261027/LPn_DecodeBounds.lean:24 | `LPl_Kit_Release.r1_wire.ValidatedRecord.mk` |
| `LPn.Decode.word_value` | evidence/leaf-p6-12-20261027/LPn_DecodeBytes.lean:8 | `LPn_Kit_word` |
| `LPn.Decode.step_good` | evidence/leaf-p6-12-20261027/LPn_DecodeBytes.lean:12 | `LPn_Kit_word` |
| `LPn.DecodeModel.values_length` | evidence/leaf-p6-12-20261027/LPn_DecodeLaws.lean:8 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.DecodeModel.first_error_bound` | evidence/leaf-p6-12-20261027/LPn_DecodeLaws.lean:11 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.DecodeModel.accepted_values` | evidence/leaf-p6-12-20261027/LPn_DecodeLaws.lean:15 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.DecodeModel.values_eq_map` | evidence/leaf-p6-12-20261027/LPn_DecodeModel.lean:15 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.DecodeModel.values_eq_fold` | evidence/leaf-p6-12-20261027/LPn_DecodeModel.lean:18 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.DecodeModel.shipped_leaf_model` | evidence/leaf-p6-12-20261027/LPn_DecodeModel.lean:22 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.predicate_eq` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:12 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.length` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:26 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.Decode.invariant` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:32 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.output` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:49 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.unique` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:61 | `LPl_Kit_Release.aspis_core.field.QM31` |
| `LPn.Decode.update_write` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:70 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.total` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:76 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.write_of_local` | evidence/leaf-p6-12-20261027/LPn_DecodeOutput.lean:98 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.native_success` | evidence/leaf-p6-12-20261027/LPn_DecodeResult.lean:14 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.native_error` | evidence/leaf-p6-12-20261027/LPn_DecodeResult.lean:29 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.row_error` | evidence/leaf-p6-12-20261027/LPn_DecodeResult.lean:43 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.arithmetic_error` | evidence/leaf-p6-12-20261027/LPn_DecodeResult.lean:48 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Decode.range_error` | evidence/leaf-p6-12-20261027/LPn_DecodeResult.lean:54 | `LPl_Kit_FieldExternal.qzero` |
| `LPn.Dot.native_result` | evidence/leaf-p6-12-20261027/LPn_DotClosed.lean:10 | `fast_pairing.canonical.Dot.push` |
| `LPn.Dot.model_raw` | evidence/leaf-p6-12-20261027/LPn_DotJoin.lean:9 | `LPn_Kit_raw` |
| `LPn.Dot.raw_same` | evidence/leaf-p6-12-20261027/LPn_DotJoin.lean:15 | `LPn_Kit_raw` |
| `LPn.DotState.update_eq` | evidence/leaf-p6-12-20261027/LPn_DotState.lean:9 | `LPn_Kit_u64` |
| `LPn.DotState.model` | evidence/leaf-p6-12-20261027/LPn_DotState.lean:20 | `LPl_Kit_Release.fast_pairing.canonical.Dot.mk` |
| `LPn.DotState.source` | evidence/leaf-p6-12-20261027/LPn_DotState.lean:35 | `LPl_Kit_Release.fast_pairing.canonical.Dot.mk` |
| `LPn.Expand.native_result` | evidence/leaf-p6-12-20261027/LPn_ExpandTrace.lean:40 | `compact.expand_values` |
| `LPn.Expand.length_error` | evidence/leaf-p6-12-20261027/LPn_ExpandTrace.lean:54 | `LPl_Kit_Release.compact.CodecError.Length` |
| `LPn.Bytes.word_val` | evidence/leaf-p6-12-20261027/LPn_Word.lean:7 | `LPn_Kit_word` |
| `LPn.Bytes.word_canonical_iff` | evidence/leaf-p6-12-20261027/LPn_Word.lean:11 | `LPn_Kit_word` |

### Unqueried import candidates

These are conservatively withheld pending per-constant inspection; an import alone is not proof of use.

| Theorem | Source | Model module on import path |
|---|---|---|
| `LPa.Boundary.loop_eq_model` | evidence/leaf-p6-1-20261027/LPa_Boundary.lean:13 | `XRk_ByteFields` |
| `LPa.Boundary.loop_eq_fold` | evidence/leaf-p6-1-20261027/LPa_Boundary.lean:18 | `XRk_ByteFields` |
| `LPa.Boundary.actual_bound` | evidence/leaf-p6-1-20261027/LPa_Boundary.lean:25 | `XRk_ByteFields` |
| `LPa.Boundary.loop_pure` | evidence/leaf-p6-1-20261027/LPa_BoundaryPure.lean:9 | `XRk_ByteFields` |
| `LPa.Boundary.field_zero` | evidence/leaf-p6-1-20261027/LPa_BoundaryWitness.lean:8 | `XRk_ByteFields` |
| `LPa.Boundary.fold_zero` | evidence/leaf-p6-1-20261027/LPa_BoundaryWitness.lean:10 | `XRk_ByteFields` |
| `LPa.Boundary.zero_accepted` | evidence/leaf-p6-1-20261027/LPa_BoundaryWitness.lean:19 | `XRk_ByteFields` |
| `LPa.Circle.leaf_eq_reference` | evidence/leaf-p6-1-20261027/LPa_Circle.lean:17 | `XRk_CircleModel` |
| `LPa.Circle.error_independent` | evidence/leaf-p6-1-20261027/LPa_Circle.lean:22 | `XRk_CircleModel` |
| `LPa.Claims.loop_eq_fold` | evidence/leaf-p6-1-20261027/LPa_Claims.lean:23 | `XRk_ByteFields` |
| `LPa.Claims.leaf_call_order` | evidence/leaf-p6-1-20261027/LPa_Claims.lean:29 | `XRk_ByteFields` |
| `LPa.Claims.fromRecord_spec` | evidence/leaf-p6-1-20261027/LPa_ClaimsFold.lean:17 | `XRk_ByteFields` |
| `LPa.Claims.leaf_eq_loop` | evidence/leaf-p6-1-20261027/LPa_ClaimsFold.lean:57 | `XRk_ByteFields` |
| `LPa.Decode.values_eq_map` | evidence/leaf-p6-1-20261027/LPa_Decode.lean:15 | `XRk_ByteFields` |
| `LPa.Decode.values_eq_fold` | evidence/leaf-p6-1-20261027/LPa_Decode.lean:18 | `XRk_ByteFields` |
| `LPa.Decode.shipped_leaf_model` | evidence/leaf-p6-1-20261027/LPa_Decode.lean:22 | `XRk_ByteFields` |
| `LPa.Decode.values_length` | evidence/leaf-p6-1-20261027/LPa_DecodeLaws.lean:8 | `XRk_ByteFields` |
| `LPa.Decode.first_error_bound` | evidence/leaf-p6-1-20261027/LPa_DecodeLaws.lean:11 | `XRk_ByteFields` |
| `LPa.Decode.accepted_values` | evidence/leaf-p6-1-20261027/LPa_DecodeLaws.lean:15 | `XRk_ByteFields` |
| `LPa.Dot.loop_eq_map` | evidence/leaf-p6-1-20261027/LPa_Dot.lean:14 | `XRk_ByteFields` |
| `LPa.Dot.loop_eq_fold` | evidence/leaf-p6-1-20261027/LPa_Dot.lean:16 | `XRk_ByteFields` |
| `LPa.Dot.shipped_leaf_model` | evidence/leaf-p6-1-20261027/LPa_Dot.lean:18 | `XRk_ByteFields` |
| `LPa.Dot.loop_length` | evidence/leaf-p6-1-20261027/LPa_DotTotal.lean:8 | `XRk_ByteFields` |
| `LPa.Dot.model_total` | evidence/leaf-p6-1-20261027/LPa_DotTotal.lean:11 | `XRk_ByteFields` |
| `LPa.Nonvacuity.check_accepts` | evidence/leaf-p6-1-20261027/LPa_Nonvacuity.lean:12 | `XRk_ByteFields` |
| `LPa.Nonvacuity.echeck_accepts` | evidence/leaf-p6-1-20261027/LPa_Nonvacuity.lean:13 | `XRk_ByteFields` |
| `LPa.Nonvacuity.validate_accepts` | evidence/leaf-p6-1-20261027/LPa_Nonvacuity.lean:14 | `XRk_ByteFields` |
| `LPa.Nonvacuity.invalid_row_reached` | evidence/leaf-p6-1-20261027/LPa_Nonvacuity.lean:16 | `XRk_ByteFields` |
| `LPa.Slices.range_success` | evidence/leaf-p6-1-20261027/LPa_Slices.lean:10 | `XRk_ByteFields` |
| `LPa.Slices.segment_length` | evidence/leaf-p6-1-20261027/LPa_Slices.lean:15 | `XRk_ByteFields` |
| `LPa.View.inactive_reject` | evidence/leaf-p6-1-20261027/LPa_View.lean:8 | `XRk_ByteFields` |
| `LPa.View.success` | evidence/leaf-p6-1-20261027/LPa_View.lean:14 | `XRk_ByteFields` |
| `LPa.View.frozen_success` | evidence/leaf-p6-1-20261027/LPa_ViewFrozen.lean:15 | `XRk_ByteFields` |
| `LPa.View.frozen_reject` | evidence/leaf-p6-1-20261027/LPa_ViewRejected.lean:8 | `XRk_ByteFields` |
| `LPa.Bytes.word_val` | evidence/leaf-p6-1-20261027/LPa_Word.lean:7 | `XRk_ByteFields` |
| `LPa.Bytes.word_canonical_iff` | evidence/leaf-p6-1-20261027/LPa_Word.lean:11 | `XRk_ByteFields` |
| `LPb_ByteFold.scalar_words` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:12 | `XRk_CircleModel` |
| `LPb_ByteFold.append_spec` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:14 | `XRk_CircleModel` |
| `LPb_ByteFold.weights_sequence` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:23 | `XRk_CircleModel` |
| `LPb_ByteFold.word_length` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:27 | `XRk_CircleModel` |
| `LPb_ByteFold.scalar_length` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:30 | `XRk_CircleModel` |
| `LPb_ByteFold.scalars_length` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:33 | `XRk_CircleModel` |
| `LPb_ByteFold.weights64` | evidence/leaf-p6-2-20261027/LPb_ByteFold.lean:41 | `XRk_CircleModel` |
| `LPb_CheckpointAttempts.first_failure` | evidence/leaf-p6-2-20261027/LPb_CheckpointAttempts.lean:8 | `XRk_CircleModel` |
| `LPb_CheckpointAttempts.second_failure` | evidence/leaf-p6-2-20261027/LPb_CheckpointAttempts.lean:14 | `XRk_CircleModel` |
| `LPb_CheckpointAttempts.successful_stages` | evidence/leaf-p6-2-20261027/LPb_CheckpointAttempts.lean:22 | `XRk_CircleModel` |
| `LPb_CheckpointFinalValue.finish_value` | evidence/leaf-p6-2-20261027/LPb_CheckpointFinalValue.lean:10 | `XRk_CircleModel` |
| `LPb_CheckpointFinalValue.value` | evidence/leaf-p6-2-20261027/LPb_CheckpointFinalValue.lean:17 | `XRk_CircleModel` |
| `LPb_CheckpointLayout.slice_value` | evidence/leaf-p6-2-20261027/LPb_CheckpointLayout.lean:35 | `XRk_CircleModel` |
| `LPb_CheckpointNativeGap.model_trace_bytes` | evidence/leaf-p6-2-20261027/LPb_CheckpointNativeGap.lean:9 | `XRk_CircleModel` |
| `LPb_CheckpointPrefixes.wide_failure` | evidence/leaf-p6-2-20261027/LPb_CheckpointPrefixes.lean:8 | `XRk_CircleModel` |
| `LPb_CheckpointPrefixes.payload_failure` | evidence/leaf-p6-2-20261027/LPb_CheckpointPrefixes.lean:18 | `XRk_CircleModel` |
| `LPb_CheckpointPrefixes.checksum_failure` | evidence/leaf-p6-2-20261027/LPb_CheckpointPrefixes.lean:29 | `XRk_CircleModel` |
| `LPb_CheckpointSequence.checkpoint_model_stages` | evidence/leaf-p6-2-20261027/LPb_CheckpointSequence.lean:28 | `XRk_CircleModel` |
| `LPb_CheckpointSequence.erase` | evidence/leaf-p6-2-20261027/LPb_CheckpointSequence.lean:44 | `XRk_CircleModel` |
| `LPb_ClaimFailure.stopped_fold` | evidence/leaf-p6-2-20261027/LPb_ClaimFailure.lean:8 | `XRk_ByteFields` |
| `LPb_ClaimFailure.stopped_finish` | evidence/leaf-p6-2-20261027/LPb_ClaimFailure.lean:16 | `XRk_ByteFields` |
| `LPb_ClaimStages.part_model_stages` | evidence/leaf-p6-2-20261027/LPb_ClaimStages.lean:43 | `XRk_ByteFields` |
| `LPb_ClaimStages.stopped_step` | evidence/leaf-p6-2-20261027/LPb_ClaimStages.lean:47 | `XRk_ByteFields` |
| `LPb_CollectLengths.none_absorbing` | evidence/leaf-p6-2-20261027/LPb_CollectLengths.lean:12 | `XRk_CircleModel` |
| `LPb_CollectLengths.length_of_success` | evidence/leaf-p6-2-20261027/LPb_CollectLengths.lean:18 | `XRk_CircleModel` |
| `LPb_FoldStages.congr` | evidence/leaf-p6-2-20261027/LPb_FoldStages.lean:6 | `XRk_ByteFields` |
| `LPb_FoldStages.powers_zero` | evidence/leaf-p6-2-20261027/LPb_FoldStages.lean:15 | `XRk_ByteFields` |
| `LPb_FoldStages.powers_one` | evidence/leaf-p6-2-20261027/LPb_FoldStages.lean:16 | `XRk_ByteFields` |
| `LPb_FoldStages.powers_next` | evidence/leaf-p6-2-20261027/LPb_FoldStages.lean:17 | `XRk_ByteFields` |
| `LPb_FoldStages.powers_seven` | evidence/leaf-p6-2-20261027/LPb_FoldStages.lean:24 | `XRk_ByteFields` |
| `LPb_ListWidths.flatMap_length` | evidence/leaf-p6-2-20261027/LPb_ListWidths.lean:5 | `XRk_CircleModel` |
| `LPb_ListWidths.array_bytes` | evidence/leaf-p6-2-20261027/LPb_ListWidths.lean:14 | `XRk_CircleModel` |
| `LPb_Logged.erase_bind` | evidence/leaf-p6-2-20261027/LPb_Logged.lean:15 | `XRk_CircleModel` |
| `LPb_Logged.bind_ok` | evidence/leaf-p6-2-20261027/LPb_Logged.lean:20 | `XRk_CircleModel` |
| `LPb_Logged.bind_failure` | evidence/leaf-p6-2-20261027/LPb_Logged.lean:23 | `XRk_CircleModel` |
| `LPb_Logged.bind_diverge` | evidence/leaf-p6-2-20261027/LPb_Logged.lean:26 | `XRk_CircleModel` |
| `LPb_Logged.attempted_failure` | evidence/leaf-p6-2-20261027/LPb_Logged.lean:29 | `XRk_CircleModel` |
| `LPb_Nonvacuity.query_domain` | evidence/leaf-p6-2-20261027/LPb_Nonvacuity.lean:7 | `XRk_CircleModel` |
| `LPb_Nonvacuity.scalar_index_domain` | evidence/leaf-p6-2-20261027/LPb_Nonvacuity.lean:8 | `XRk_CircleModel` |
| `LPb_Nonvacuity.weight_index_domain` | evidence/leaf-p6-2-20261027/LPb_Nonvacuity.lean:9 | `XRk_CircleModel` |
| `LPb_Nonvacuity.scalar_rejection_domain` | evidence/leaf-p6-2-20261027/LPb_Nonvacuity.lean:10 | `XRk_CircleModel` |
| `LPb_Nonvacuity.attempted_failure_witness` | evidence/leaf-p6-2-20261027/LPb_Nonvacuity.lean:12 | `XRk_CircleModel` |
| `LPb_PayloadWidth.payload_width` | evidence/leaf-p6-2-20261027/LPb_PayloadWidth.lean:8 | `XRk_CircleModel` |
| `LPb_PreparedSequence.prepared_model_stages` | evidence/leaf-p6-2-20261027/LPb_PreparedSequence.lean:29 | `XRk_ByteFields` |
| `LPb_PreparedWitness.powers_length` | evidence/leaf-p6-2-20261027/LPb_PreparedWitness.lean:16 | `XRk_ByteFields` |
| `LPb_PreparedWitness.trace` | evidence/leaf-p6-2-20261027/LPb_PreparedWitness.lean:32 | `XRk_ByteFields` |
| `LPb_ResultInversion.bind_success` | evidence/leaf-p6-2-20261027/LPb_ResultInversion.lean:5 | `XRk_CircleModel` |
| `LPc.Nonvacuity.zero_canonical` | evidence/leaf-p6-3-20261027/LPc_Audit.lean:18 | `XRk_ByteFields` |
| `LPc.Nonvacuity.boundary_inhabited` | evidence/leaf-p6-3-20261027/LPc_Audit.lean:21 | `XRk_ByteFields` |
| `LPc.Boundary.decoded_canonical` | evidence/leaf-p6-3-20261027/LPc_BoundaryProducer.lean:8 | `XRk_ByteFields` |
| `LPc.Decode.step_canonical` | evidence/leaf-p6-3-20261027/LPc_DecodeCanonical.lean:7 | `XRk_ByteFields` |
| `LPc.Decode.success_canonical` | evidence/leaf-p6-3-20261027/LPc_DecodeSuccess.lean:6 | `XRk_ByteFields` |
| `LPc.Decode.values_get` | evidence/leaf-p6-3-20261027/LPc_DecodeValues.lean:6 | `XRk_ByteFields` |
| `LPc.Decode.values_canonical` | evidence/leaf-p6-3-20261027/LPc_DecodeValues.lean:12 | `XRk_ByteFields` |
| `LPc.View.readset` | evidence/leaf-p6-3-20261027/LPc_ViewFrame.lean:6 | `XRk_ByteFields` |
| `LPg.good_prefix` | evidence/leaf-p6-7-20261027/LPg_Nonvacuity.lean:6 | `XRk_ByteFields` |
| `LPg.error_prefix` | evidence/leaf-p6-7-20261027/LPg_Nonvacuity.lean:11 | `XRk_ByteFields` |
| `LPg.four_products` | evidence/leaf-p6-7-20261027/LPg_Nonvacuity.lean:18 | `XRk_ByteFields` |
| `LPg.partial_fold` | evidence/leaf-p6-7-20261027/LPg_Nonvacuity.lean:28 | `XRk_ByteFields` |
| `AspisR1.LPh.Model.raw_words` | evidence/leaf-p6-8-20261027/LPh_ModelPort.lean:16 | `XRk_ByteFields` |
| `AspisR1.LPh.Model.scanner_contract_inhabited` | evidence/leaf-p6-8-20261027/LPh_ModelPort.lean:22 | `XRk_ByteFields` |
| `AspisR1.LPh.Model.canonical_domain_inhabited` | evidence/leaf-p6-8-20261027/LPh_ModelPort.lean:30 | `XRk_ByteFields` |
| `LPl.coimport_identity` | evidence/leaf-p6-10-20261027/LPl_Coimport.lean:6 | `LPl_Kit_FunsExternal` |
| `LPl.Echeck.zero_chunk` | evidence/leaf-p6-10-20261027/LPl_EcheckWitness.lean:7 | `LPl_Kit_FunsExternal` |
| `LPl.Echeck.rejected_chunk` | evidence/leaf-p6-10-20261027/LPl_EcheckWitness.lean:9 | `LPl_Kit_FunsExternal` |
| `LPl.Echeck.empty_result` | evidence/leaf-p6-10-20261027/LPl_EcheckWitness.lean:12 | `LPl_Kit_FunsExternal` |
| `LPl.Expand.covered` | evidence/leaf-p6-10-20261027/LPl_ExpandClasses.lean:6 | `LPl_Kit_FunsExternal` |
| `LPl.Expand.caller_rows` | evidence/leaf-p6-10-20261027/LPl_ExpandClasses.lean:12 | `LPl_Kit_FunsExternal` |
| `LPl_G.validation_error` | evidence/leaf-p6-10-20261027/LPl_G_Validation.lean:7 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.bad_eq` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:10 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.window` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:13 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.first_error` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:18 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.native_result` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:25 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.error_bound` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:37 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.earlier_error` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:45 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.unique` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:52 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.total` | evidence/leaf-p6-10-20261027/LPl_Validate.lean:57 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.native_success` | evidence/leaf-p6-10-20261027/LPl_ValidateAudit.lean:7 | `LPl_Kit_FunsExternal` |
| `LPl.Validate.native_error` | evidence/leaf-p6-10-20261027/LPl_ValidateAudit.lean:12 | `LPl_Kit_FunsExternal` |
| `LPo.BA.Add.word_val_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPa_AddFormula.lean:6 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Add.word_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPa_AddInvariant.lean:11 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Add.field_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPa_AddInvariant.lean:16 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Add.fold_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPa_AddInvariant.lean:23 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Boundary.loop_eq_model` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Boundary.lean:13 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Boundary.loop_eq_fold` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Boundary.lean:18 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Boundary.actual_bound` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Boundary.lean:25 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Boundary.loop_pure` | evidence/leaf-p6-13-20261027/LPo_B_LPa_BoundaryPure.lean:9 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Add.model_word` | evidence/leaf-p6-13-20261027/LPo_B_LPa_CanonicalAdd.lean:11 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Add.model_pair` | evidence/leaf-p6-13-20261027/LPo_B_LPa_CanonicalAdd.lean:17 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Add.model_field` | evidence/leaf-p6-13-20261027/LPo_B_LPa_CanonicalAdd.lean:24 | `LPl_Kit_FieldExternal` |
| `LPo.BA.Decode.values_eq_map` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Decode.lean:15 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Decode.values_eq_fold` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Decode.lean:18 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Decode.shipped_leaf_model` | evidence/leaf-p6-13-20261027/LPo_B_LPa_Decode.lean:22 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Decode.values_length` | evidence/leaf-p6-13-20261027/LPo_B_LPa_DecodeLaws.lean:8 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Decode.first_error_bound` | evidence/leaf-p6-13-20261027/LPo_B_LPa_DecodeLaws.lean:11 | `LPn_Kit_DecodeModels` |
| `LPo.BA.Decode.accepted_values` | evidence/leaf-p6-13-20261027/LPo_B_LPa_DecodeLaws.lean:15 | `LPn_Kit_DecodeModels` |
| `LPo.BC.Boundary.decoded_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPc_BoundaryProducer.lean:8 | `LPn_Kit_DecodeModels` |
| `LPo.BC.Decode.step_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPc_DecodeCanonical.lean:7 | `LPn_Kit_DecodeModels` |
| `LPo.BC.Decode.success_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPc_DecodeSuccess.lean:6 | `LPn_Kit_DecodeModels` |
| `LPo.BC.Decode.values_get` | evidence/leaf-p6-13-20261027/LPo_B_LPc_DecodeValues.lean:6 | `LPn_Kit_DecodeModels` |
| `LPo.BC.Decode.values_canonical` | evidence/leaf-p6-13-20261027/LPo_B_LPc_DecodeValues.lean:12 | `LPn_Kit_DecodeModels` |
| `LPo.Boundary.exact_result` | evidence/leaf-p6-13-20261027/LPo_Boundary.lean:9 | `LPn_Kit_DecodeModels` |
| `LPo.Boundary.decoded_exact` | evidence/leaf-p6-13-20261027/LPo_Boundary.lean:17 | `LPn_Kit_DecodeModels` |
| `LPo.Boundary.decoded_unique` | evidence/leaf-p6-13-20261027/LPo_Boundary.lean:30 | `LPn_Kit_DecodeModels` |
| `LPo.Boundary.caller_row` | evidence/leaf-p6-13-20261027/LPo_Boundary.lean:37 | `LPn_Kit_DecodeModels` |
| `LPo.Circle.exponent_two` | evidence/leaf-p6-13-20261027/LPo_CircleObstruction.lean:8 | `LPo_CircleModel` |
| `LPo.Circle.square_two` | evidence/leaf-p6-13-20261027/LPo_CircleObstruction.lean:14 | `LPo_CircleModel` |
| `LPo.Circle.pow_square_law_false` | evidence/leaf-p6-13-20261027/LPo_CircleObstruction.lean:16 | `LPo_CircleModel` |
| `LPo.View.decoded_eq` | evidence/leaf-p6-13-20261027/LPo_Readset.lean:14 | `LPn_Kit_DecodeModels` |
| `LPo.View.rest_eq` | evidence/leaf-p6-13-20261027/LPo_Readset.lean:17 | `LPn_Kit_DecodeModels` |
| `LPo.View.product_readset` | evidence/leaf-p6-13-20261027/LPo_Readset.lean:26 | `LPn_Kit_DecodeModels` |
| `LPo.View.five_range_readset` | evidence/leaf-p6-13-20261027/LPo_Readset.lean:35 | `LPn_Kit_DecodeModels` |
| `LPo.View.frozen_product` | evidence/leaf-p6-13-20261027/LPo_Readset.lean:41 | `LPn_Kit_DecodeModels` |
| `LPo.View.range_success` | evidence/leaf-p6-13-20261027/LPo_View.lean:10 | `LPn_Kit_DecodeModels` |
| `LPo.View.segment_length` | evidence/leaf-p6-13-20261027/LPo_View.lean:15 | `LPn_Kit_DecodeModels` |
| `LPo.View.decoder_spec` | evidence/leaf-p6-13-20261027/LPo_View.lean:48 | `LPn_Kit_DecodeModels` |
| `LPo.View.model_product` | evidence/leaf-p6-13-20261027/LPo_View.lean:54 | `LPn_Kit_DecodeModels` |
| `AspisR1.LPq_ArrayPorts.update` | lean/LPq_ArrayPorts.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ArrayPorts.mapped` | lean/LPq_ArrayPorts.lean:11 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ArrayPorts.canonical_set` | lean/LPq_ArrayPorts.lean:16 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_BytesTotal.read` | lean/LPq_BytesTotal.lean:10 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_BytesTotal.source` | lean/LPq_BytesTotal.lean:16 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_CarrierFacts.back_claim` | lean/LPq_CarrierFacts.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_CarrierFacts.weights_from_powers` | lean/LPq_CarrierFacts.lean:8 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_CarrierFacts.native_unique` | lean/LPq_CarrierFacts.lean:17 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_DecodeTotal.limbs` | lean/LPq_DecodeTotal.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Decoder.limbs` | lean/LPq_Decoder.lean:11 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Decoder.bytes` | lean/LPq_Decoder.lean:19 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Decoder.unwrap` | lean/LPq_Decoder.lean:28 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Decoder.field` | lean/LPq_Decoder.lean:32 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Decoder.claim_field` | lean/LPq_Decoder.lean:54 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ExpandedWords.low` | lean/LPq_ExpandedWords.lean:18 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ExpandedWords.high` | lean/LPq_ExpandedWords.lean:31 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ExpandedWords.canonical` | lean/LPq_ExpandedWords.lean:43 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_add_graph` | lean/LPq_FieldPorts.lean:12 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_sub_graph` | lean/LPq_FieldPorts.lean:20 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_mul_graph` | lean/LPq_FieldPorts.lean:28 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.by_r_graph` | lean/LPq_FieldPorts.lean:36 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_add` | lean/LPq_FieldPorts.lean:44 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_sub` | lean/LPq_FieldPorts.lean:50 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.cm_mul` | lean/LPq_FieldPorts.lean:56 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_FieldPorts.by_r` | lean/LPq_FieldPorts.lean:62 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_IndexPorts.add` | lean/LPq_IndexPorts.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_IndexPorts.mul` | lean/LPq_IndexPorts.lean:17 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OuterConstruct.loop` | lean/LPq_OuterConstruct.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OuterTrace.point_source` | lean/LPq_OuterTrace.lean:27 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OuterTrace.source` | lean/LPq_OuterTrace.lean:40 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OutputDomains.finish` | lean/LPq_OutputDomains.lean:7 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OutputDomains.point` | lean/LPq_OutputDomains.lean:21 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_OutputDomains.powers` | lean/LPq_OutputDomains.lean:32 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PointConstruct.loop` | lean/LPq_PointConstruct.lean:18 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PointConstruct.from_zero` | lean/LPq_PointConstruct.lean:60 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.loop` | lean/LPq_Powers.lean:7 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.one_canonical` | lean/LPq_Powers.lean:39 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.zero_port` | lean/LPq_Powers.lean:44 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.one_port` | lean/LPq_Powers.lean:50 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.map_ports` | lean/LPq_Powers.lean:57 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Powers.source` | lean/LPq_Powers.lean:67 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PowersStep.step` | lean/LPq_PowersStep.lean:8 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedClaim.program_eq` | lean/LPq_PreparedClaim.lean:16 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedClaim.native_result` | lean/LPq_PreparedClaim.lean:27 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedClaim.uniqueness` | lean/LPq_PreparedClaim.lean:36 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedTrace.zero_claim` | lean/LPq_PreparedTrace.lean:11 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedTrace.initial_canonical` | lean/LPq_PreparedTrace.lean:14 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedTrace.construct` | lean/LPq_PreparedTrace.lean:32 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_PreparedTrace.source` | lean/LPq_PreparedTrace.lean:47 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ReadPorts.q_roundtrip` | lean/LPq_ReadPorts.lean:9 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ReadPorts.e_roundtrip` | lean/LPq_ReadPorts.lean:10 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ReadPorts.weights` | lean/LPq_ReadPorts.lean:20 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ReadPorts.semantic` | lean/LPq_ReadPorts.lean:28 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ReadPorts.five_domains` | lean/LPq_ReadPorts.lean:50 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.add` | lean/LPq_ScalarPorts.lean:7 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.sub` | lean/LPq_ScalarPorts.lean:12 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.reduce` | lean/LPq_ScalarPorts.lean:17 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.wrapper` | lean/LPq_ScalarPorts.lean:22 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.mul` | lean/LPq_ScalarPorts.lean:26 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_ScalarPorts.double` | lean/LPq_ScalarPorts.lean:30 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_SelectedDomain.selected_fields` | lean/LPq_SelectedDomain.lean:18 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_SelectedDomain.native_result` | lean/LPq_SelectedDomain.lean:30 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_SixPoints.selected` | lean/LPq_SixPoints.lean:12 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_SixPoints.domain` | lean/LPq_SixPoints.lean:25 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_SixPoints.construct` | lean/LPq_SixPoints.lean:36 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_TowerPorts.add` | lean/LPq_TowerPorts.lean:6 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_TowerPorts.sub` | lean/LPq_TowerPorts.lean:14 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_TowerPorts.mul` | lean/LPq_TowerPorts.lean:22 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_TowerPorts.mul_u` | lean/LPq_TowerPorts.lean:38 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Weighted.paired` | lean/LPq_Weighted.lean:15 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Weighted.zero_canonical` | lean/LPq_Weighted.lean:30 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Weighted.zero_wide` | lean/LPq_Weighted.lean:34 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_Weighted.source` | lean/LPq_Weighted.lean:40 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WeightedStep.add` | lean/LPq_WeightedStep.lean:7 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WeightedStep.canonical_port` | lean/LPq_WeightedStep.lean:24 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WeightedStep.paired` | lean/LPq_WeightedStep.lean:40 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WidePorts.canonical` | lean/LPq_WidePorts.lean:7 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WidePorts.mul` | lean/LPq_WidePorts.lean:9 | `XRn_Join_QueryModel` |
| `AspisR1.LPq_WidePorts.loop_mul` | lean/LPq_WidePorts.lean:38 | `XRn_Join_QueryModel` |
| `XRk_Association.preparedScratchProjection` | evidence/extraction-assoc3-20261027/XRk_Association.lean:70 | `XRk_CircleModel` |
| `XRk_Association.preparedClaimPowersAssociation` | evidence/extraction-assoc3-20261027/XRk_Association.lean:80 | `XRk_CircleModel` |
| `XRk_CanonicalScalar.checked` | evidence/extraction-assoc3-20261027/XRk_CanonicalScalar.lean:9 | `XRk_CircleModel` |
| `XRk_ClaimTrace.powers_length` | evidence/extraction-assoc3-20261027/XRk_ClaimTrace.lean:14 | `XRk_CircleModel` |
| `XRk_ClaimTrace.trace` | evidence/extraction-assoc3-20261027/XRk_ClaimTrace.lean:29 | `XRk_CircleModel` |
| `XRk_DotCells.sum_cell` | evidence/extraction-assoc3-20261027/XRk_DotCells.lean:7 | `XRk_CircleModel` |
| `XRk_DotProjection.push_count` | evidence/extraction-assoc3-20261027/XRk_DotProjection.lean:5 | `XRk_CircleModel` |
| `XRk_DotProjection.dotCountProjection` | evidence/extraction-assoc3-20261027/XRk_DotProjection.lean:33 | `XRk_CircleModel` |
| `XRk_DotReject.limit_frame` | evidence/extraction-assoc3-20261027/XRk_DotReject.lean:5 | `XRk_CircleModel` |
| `XRk_DotReject.invalid_scalar` | evidence/extraction-assoc3-20261027/XRk_DotReject.lean:13 | `XRk_CircleModel` |
| `XRk_EmptyGeometry.run` | evidence/extraction-assoc3-20261027/XRk_EmptyGeometry.lean:11 | `XRk_CircleModel` |
| `XRk_GeometryMeasure.advance` | evidence/extraction-assoc3-20261027/XRk_GeometryMeasure.lean:6 | `XRk_CircleModel` |
| `XRk_GeometryProjection.loop_start` | evidence/extraction-assoc3-20261027/XRk_GeometryProjection.lean:8 | `XRk_CircleModel` |
| `XRk_GeometryProjection.start` | evidence/extraction-assoc3-20261027/XRk_GeometryProjection.lean:20 | `XRk_CircleModel` |
| `XRk_GeometryStep.step` | evidence/extraction-assoc3-20261027/XRk_GeometryStep.lean:10 | `XRk_CircleModel` |
| `XRk_Nonvacuity.canonical_zero_domain` | evidence/extraction-assoc3-20261027/XRk_Nonvacuity.lean:7 | `XRk_CircleModel` |
| `XRk_Nonvacuity.below_dot_bound` | evidence/extraction-assoc3-20261027/XRk_Nonvacuity.lean:12 | `XRk_CircleModel` |
| `XRk_Nonvacuity.invalid_row_is_reached` | evidence/extraction-assoc3-20261027/XRk_Nonvacuity.lean:15 | `XRk_CircleModel` |
| `XRk_Nonvacuity.accepted_empty_geometry` | evidence/extraction-assoc3-20261027/XRk_Nonvacuity.lean:18 | `XRk_CircleModel` |
| `XRk_PowersAssociation.powers` | evidence/extraction-assoc3-20261027/XRk_PowersAssociation.lean:6 | `XRk_CircleModel` |
| `XRk_PowersLoop.suffix` | evidence/extraction-assoc3-20261027/XRk_PowersLoop.lean:10 | `XRk_CircleModel` |
| `XRk_PrepareProjection.constructor` | evidence/extraction-assoc3-20261027/XRk_PrepareProjection.lean:8 | `XRk_CircleModel` |
| `XRk_PushTrace.accepted` | evidence/extraction-assoc3-20261027/XRk_PushTrace.lean:5 | `XRk_CircleModel` |
| `XRk_RejectedScratch.rejected_scratch` | evidence/extraction-assoc3-20261027/XRk_RejectedScratch.lean:5 | `XRk_CircleModel` |
| `XRk_ScratchProjection.accepted_powers` | evidence/extraction-assoc3-20261027/XRk_ScratchProjection.lean:8 | `XRk_CircleModel` |
| `XRk_Tx1Association.candidateTx1AcceptedPath` | evidence/extraction-assoc3-20261027/XRk_Tx1Association.lean:6 | `XRk_CircleModel` |
| `XRk_Tx1Association.acceptedCandidateCheckpoint` | evidence/extraction-assoc3-20261027/XRk_Tx1Association.lean:11 | `XRk_CircleModel` |
| `XRk_Tx1Projection.cuts` | evidence/extraction-assoc3-20261027/XRk_Tx1Projection.lean:6 | `XRk_CircleModel` |
| `XRk_VectorLength.push` | evidence/extraction-assoc3-20261027/XRk_VectorLength.lean:7 | `XRk_CircleModel` |
| `XRl_Adapter.fromFnState` | evidence/extraction-assoc4-20261027/XRl_Adapter.lean:16 | `XRk_ByteFields` |
| `XRl_Adapter.intoIter` | evidence/extraction-assoc4-20261027/XRl_Adapter.lean:31 | `XRk_ByteFields` |
| `XRl_Adapter.revRestored` | evidence/extraction-assoc4-20261027/XRl_Adapter.lean:41 | `XRk_ByteFields` |
| `XRl_Adapter.enumerateRestored` | evidence/extraction-assoc4-20261027/XRl_Adapter.lean:48 | `XRk_ByteFields` |
| `XRl_Adapter.enumerateNext` | evidence/extraction-assoc4-20261027/XRl_Adapter.lean:64 | `XRk_ByteFields` |
| `XRl_Adapter.exhausted_original` | evidence/extraction-assoc4-20261027/XRl_AdapterCounterexample.lean:22 | `XRk_ByteFields` |
| `XRl_Adapter.exhausted_adapted` | evidence/extraction-assoc4-20261027/XRl_AdapterCounterexample.lean:24 | `XRk_ByteFields` |
| `XRl_Adapter.next_back_not_equivalent` | evidence/extraction-assoc4-20261027/XRl_AdapterCounterexample.lean:28 | `XRk_ByteFields` |
| `XRl_Adapter.exhausted_reachable` | evidence/extraction-assoc4-20261027/XRl_AdapterCounterexample.lean:36 | `XRk_ByteFields` |
| `XRl_Adapter.reverseNext_not_equivalent` | evidence/extraction-assoc4-20261027/XRl_AdapterCounterexample.lean:43 | `XRk_ByteFields` |
| `XRl_Adapter.next_projection` | evidence/extraction-assoc4-20261027/XRl_AdapterErasure.lean:13 | `XRk_ByteFields` |
| `XRl_Adapter.next_back_projection` | evidence/extraction-assoc4-20261027/XRl_AdapterErasure.lean:21 | `XRk_ByteFields` |
| `XRl_Adapter.restoration_not_erasable` | evidence/extraction-assoc4-20261027/XRl_AdapterErasure.lean:38 | `XRk_ByteFields` |
| `XRl_CanonicalConstructors.remainder` | evidence/extraction-assoc4-20261027/XRl_CanonicalConstructors.lean:7 | `XRk_CircleModel` |
| `XRl_CanonicalConstructors.canon` | evidence/extraction-assoc4-20261027/XRl_CanonicalConstructors.lean:15 | `XRk_CircleModel` |
| `XRl_CanonicalConstructors.new` | evidence/extraction-assoc4-20261027/XRl_CanonicalConstructors.lean:27 | `XRk_CircleModel` |
| `XRl_CanonicalConstructors.from_qm31` | evidence/extraction-assoc4-20261027/XRl_CanonicalConstructors.lean:36 | `XRk_CircleModel` |
| `XRl_CheckpointBytes.word_length` | evidence/extraction-assoc4-20261027/XRl_CheckpointBytes.lean:8 | `XRk_CircleModel` |
| `XRl_CheckpointBytes.q_length` | evidence/extraction-assoc4-20261027/XRl_CheckpointBytes.lean:11 | `XRk_CircleModel` |
| `XRl_CheckpointBytes.wide_total` | evidence/extraction-assoc4-20261027/XRl_CheckpointBytes.lean:14 | `XRk_CircleModel` |
| `XRl_CheckpointFinalizer.size` | evidence/extraction-assoc4-20261027/XRl_CheckpointFinalizer.lean:6 | `XRk_CircleModel` |
| `XRl_Adapter.closure_1_FnMut` | evidence/extraction-assoc4-20261027/XRl_ClosureAdapter.lean:17 | `XRk_CircleModel` |
| `XRl_Adapter.closure_1_FnOnce_projection` | evidence/extraction-assoc4-20261027/XRl_ClosureAdapter.lean:27 | `XRk_CircleModel` |
| `XRl_Adapter.closure_1_mut_once` | evidence/extraction-assoc4-20261027/XRl_ClosureAdapter.lean:37 | `XRk_CircleModel` |
| `XRl_Adapter.closure_1_restoration` | evidence/extraction-assoc4-20261027/XRl_ClosureCapture.lean:9 | `XRk_CircleModel` |
| `XRl_DotAssociation.reached` | evidence/extraction-assoc4-20261027/XRl_DotAssociation.lean:8 | `XRk_CircleModel` |
| `XRl_DotHistory.initial_count` | evidence/extraction-assoc4-20261027/XRl_DotHistory.lean:17 | `XRk_CircleModel` |
| `XRl_DotHistory.count` | evidence/extraction-assoc4-20261027/XRl_DotHistory.lean:22 | `XRk_CircleModel` |
| `XRl_DotHistory.canonical_scalars` | evidence/extraction-assoc4-20261027/XRl_DotHistory.lean:39 | `XRk_CircleModel` |
| `XRl_DotSums.cells` | evidence/extraction-assoc4-20261027/XRl_DotSums.lean:16 | `XRk_CircleModel` |
| `XRl_DotSums.factor` | evidence/extraction-assoc4-20261027/XRl_DotSums.lean:41 | `XRk_CircleModel` |
| `XRl_GeometryCollect.list_length` | evidence/extraction-assoc4-20261027/XRl_GeometryCollect.lean:12 | `XRk_CircleModel` |
| `XRl_GeometryCollect.length` | evidence/extraction-assoc4-20261027/XRl_GeometryCollect.lean:23 | `XRk_CircleModel` |
| `XRl_GeometryInput.range` | evidence/extraction-assoc4-20261027/XRl_GeometryInput.lean:6 | `XRk_CircleModel` |
| `XRl_GeometryLengths.loop` | evidence/extraction-assoc4-20261027/XRl_GeometryLengths.lean:8 | `XRk_CircleModel` |
| `XRl_GeometryStep.step` | evidence/extraction-assoc4-20261027/XRl_GeometryStep.lean:15 | `XRk_CircleModel` |
| `XRl_GeometryVectors.clone` | evidence/extraction-assoc4-20261027/XRl_GeometryVectors.lean:7 | `XRk_CircleModel` |
| `XRl_GeometryVectors.extend` | evidence/extraction-assoc4-20261027/XRl_GeometryVectors.lean:13 | `XRk_CircleModel` |
| `XRl_InversionBoundary.zero_rejected` | evidence/extraction-assoc4-20261027/XRl_InversionBoundary.lean:7 | `XRk_ByteFields` |
| `XRl_InversionBoundary.success` | evidence/extraction-assoc4-20261027/XRl_InversionBoundary.lean:9 | `XRk_ByteFields` |
| `XRl_LineValues.continuation` | evidence/extraction-assoc4-20261027/XRl_LineValues.lean:8 | `XRk_CircleModel` |
| `XRl_Nonvacuity.empty_history` | evidence/extraction-assoc4-20261027/XRl_Nonvacuity.lean:8 | `XRk_CircleModel` |
| `XRl_Nonvacuity.bad_wide_history` | evidence/extraction-assoc4-20261027/XRl_Nonvacuity.lean:15 | `XRk_CircleModel` |
| `XRl_Nonvacuity.validated_wide_domain` | evidence/extraction-assoc4-20261027/XRl_Nonvacuity.lean:22 | `XRk_CircleModel` |
| `XRl_QueryGeometry.lengths` | evidence/extraction-assoc4-20261027/XRl_QueryGeometry.lean:9 | `XRk_CircleModel` |
| `XRl_QueryGeometry.queryGeometryLineInvariant` | evidence/extraction-assoc4-20261027/XRl_QueryGeometry.lean:31 | `XRk_CircleModel` |
| `XRl_RangeMeasure.terminal` | evidence/extraction-assoc4-20261027/XRl_RangeMeasure.lean:7 | `XRk_ByteFields` |
| `XRl_RangeMeasure.advance` | evidence/extraction-assoc4-20261027/XRl_RangeMeasure.lean:22 | `XRk_ByteFields` |
| `XRl_Adapter.next_back_cursor` | evidence/extraction-assoc4-20261027/XRl_ReverseCursor.lean:7 | `XRk_ByteFields` |
| `XRl_Adapter.next_back_restoration_cursor` | evidence/extraction-assoc4-20261027/XRl_ReverseCursor.lean:15 | `XRk_ByteFields` |
| `XRl_Adapter.reverseNext_at_zero` | evidence/extraction-assoc4-20261027/XRl_ReverseDomain.lean:23 | `XRk_ByteFields` |
| `XRl_Adapter.fresh_cursor` | evidence/extraction-assoc4-20261027/XRl_ReverseDomain.lean:34 | `XRk_ByteFields` |
| `XRl_SliceRemaining.terminal` | evidence/extraction-assoc4-20261027/XRl_SliceRemaining.lean:6 | `XRk_CircleModel` |
| `XRl_SliceRemaining.advance` | evidence/extraction-assoc4-20261027/XRl_SliceRemaining.lean:14 | `XRk_CircleModel` |
| `XRl_WideBoundary.invalid_coordinate` | evidence/extraction-assoc4-20261027/XRl_WideBoundary.lean:11 | `XRk_CircleModel` |
| `XRl_WideBoundary.unchecked_wide_projection` | evidence/extraction-assoc4-20261027/XRl_WideBoundary.lean:20 | `XRk_CircleModel` |
| `XRl_WideBoundary.invalid_wide_accepted` | evidence/extraction-assoc4-20261027/XRl_WideBoundary.lean:29 | `XRk_CircleModel` |
| `XRl_WideCanonical.word` | evidence/extraction-assoc4-20261027/XRl_WideCanonical.lean:8 | `XRk_CircleModel` |
| `XRl_WideCanonical.q` | evidence/extraction-assoc4-20261027/XRl_WideCanonical.lean:16 | `XRk_CircleModel` |
| `XRl_WideCanonical.from_limbs` | evidence/extraction-assoc4-20261027/XRl_WideCanonical.lean:22 | `XRk_CircleModel` |
| `XRm_ActualDot.associated` | evidence/extraction-assoc5-20261027/XRm_ActualDot.lean:7 | `XRk_CircleModel` |
| `XRm_AllocationBoundary.filled_ne_error` | evidence/extraction-assoc5-20261027/XRm_AllocationBoundary.lean:7 | `XRk_CircleModel` |
| `XRm_CandidateAssociation.source` | evidence/extraction-assoc5-20261027/XRm_CandidateAssociation.lean:9 | `XRk_CircleModel` |
| `XRm_CheckpointCalls.calls` | evidence/extraction-assoc5-20261027/XRm_CheckpointCalls.lean:5 | `XRk_CircleModel` |
| `XRm_CheckpointFinalize.value` | evidence/extraction-assoc5-20261027/XRm_CheckpointFinalize.lean:8 | `XRk_CircleModel` |
| `XRm_CheckpointCalls.slice` | evidence/extraction-assoc5-20261027/XRm_CheckpointLayout.lean:24 | `XRk_CircleModel` |
| `XRm_CheckpointSize.finish_length` | evidence/extraction-assoc5-20261027/XRm_CheckpointSize.lean:5 | `XRk_CircleModel` |
| `XRm_CheckpointSize.model` | evidence/extraction-assoc5-20261027/XRm_CheckpointSize.lean:16 | `XRk_CircleModel` |
| `XRm_CompactLength.reject` | evidence/extraction-assoc5-20261027/XRm_CompactLength.lean:6 | `XRk_CircleModel` |
| `XRm_CompactShape.accepted` | evidence/extraction-assoc5-20261027/XRm_CompactShape.lean:8 | `XRk_CircleModel` |
| `XRm_DotAssociation.canonical_iff` | evidence/extraction-assoc5-20261027/XRm_DotAssociation.lean:6 | `XRk_CircleModel` |
| `XRm_DotAssociation.prepared_tail` | evidence/extraction-assoc5-20261027/XRm_DotAssociation.lean:14 | `XRk_CircleModel` |
| `XRm_DotBounds.wrap` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:7 | `XRk_CircleModel` |
| `XRm_DotBounds.raw` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:10 | `XRk_CircleModel` |
| `XRm_DotBounds.raw_index` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:18 | `XRk_CircleModel` |
| `XRm_DotBounds.partial_bound` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:26 | `XRk_CircleModel` |
| `XRm_DotBounds.term_bound` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:35 | `XRk_CircleModel` |
| `XRm_DotBounds.u64_value` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:38 | `XRk_CircleModel` |
| `XRm_DotBounds.step_value` | evidence/extraction-assoc5-20261027/XRm_DotBounds.lean:41 | `XRk_CircleModel` |
| `XRm_DotNaturalHistory.reached` | evidence/extraction-assoc5-20261027/XRm_DotNaturalHistory.lean:7 | `XRk_CircleModel` |
| `XRm_DotNoWrap.fold` | evidence/extraction-assoc5-20261027/XRm_DotNoWrap.lean:9 | `XRk_CircleModel` |
| `XRm_DotNoWrap.zero` | evidence/extraction-assoc5-20261027/XRm_DotNoWrap.lean:37 | `XRk_CircleModel` |
| `XRm_DotNoWrap.operands_length` | evidence/extraction-assoc5-20261027/XRm_DotNoWrap.lean:46 | `XRk_CircleModel` |
| `XRm_DotSites.tail` | evidence/extraction-assoc5-20261027/XRm_DotSites.lean:15 | `XRk_CircleModel` |
| `XRm_GeometryPoint.point` | evidence/extraction-assoc5-20261027/XRm_GeometryPoint.lean:8 | `XRk_CircleModel` |
| `XRm_GeometryPoint.table_value` | evidence/extraction-assoc5-20261027/XRm_GeometryPoint.lean:31 | `XRk_CircleModel` |
| `XRm_GeometryPoint.low_index` | evidence/extraction-assoc5-20261027/XRm_GeometryPoint.lean:34 | `XRk_CircleModel` |
| `XRm_GeometryPoint.line` | evidence/extraction-assoc5-20261027/XRm_GeometryPoint.lean:39 | `XRk_CircleModel` |
| `XRm_GeometryValues.line` | evidence/extraction-assoc5-20261027/XRm_GeometryValues.lean:10 | `XRk_CircleModel` |
| `XRm_GeometryValues.z` | evidence/extraction-assoc5-20261027/XRm_GeometryValues.lean:27 | `XRk_CircleModel` |
| `XRm_QueryPoint.reached` | evidence/extraction-assoc5-20261027/XRm_LocalAudit.lean:42 | `XRk_CircleModel` |
| `XRm_Nonvacuity.reverse_prefix` | evidence/extraction-assoc5-20261027/XRm_Nonvacuity.lean:6 | `XRk_ByteFields` |
| `XRm_Nonvacuity.empty_dot` | evidence/extraction-assoc5-20261027/XRm_Nonvacuity.lean:9 | `XRk_ByteFields` |
| `XRm_Nonvacuity.canonical_one` | evidence/extraction-assoc5-20261027/XRm_Nonvacuity.lean:12 | `XRk_ByteFields` |
| `XRm_Nonvacuity.noncanonical_history` | evidence/extraction-assoc5-20261027/XRm_Nonvacuity.lean:17 | `XRk_ByteFields` |
| `XRm_PointInterpretation.array_member` | evidence/extraction-assoc5-20261027/XRm_PointInterpretation.lean:7 | `XRk_CircleModel` |
| `XRm_PointInterpretation.table_canonical` | evidence/extraction-assoc5-20261027/XRm_PointInterpretation.lean:16 | `XRk_CircleModel` |
| `XRm_PointInterpretation.point` | evidence/extraction-assoc5-20261027/XRm_PointInterpretation.lean:26 | `XRk_CircleModel` |
| `XRm_PowersCanonical.recurrence` | evidence/extraction-assoc5-20261027/XRm_PowersCanonical.lean:9 | `XRk_CircleModel` |
| `XRm_PowersCanonical.powers` | evidence/extraction-assoc5-20261027/XRm_PowersCanonical.lean:38 | `XRk_CircleModel` |
| `XRm_PowersCanonical.prepared` | evidence/extraction-assoc5-20261027/XRm_PowersCanonical.lean:48 | `XRk_CircleModel` |
| `XRm_PowersCanonical.array_read` | evidence/extraction-assoc5-20261027/XRm_PowersCanonical.lean:55 | `XRk_CircleModel` |
| `XRm_QueryIndices.reached` | evidence/extraction-assoc5-20261027/XRm_QueryIndices.lean:5 | `XRk_CircleModel` |
| `XRm_QueryLineStep.continuation` | evidence/extraction-assoc5-20261027/XRm_QueryLineStep.lean:11 | `XRk_CircleModel` |
| `XRm_ResultCuts.map_err_ok` | evidence/extraction-assoc5-20261027/XRm_ResultCuts.lean:6 | `XRk_CircleModel` |
| `XRm_ResultCuts.fibre` | evidence/extraction-assoc5-20261027/XRm_ResultCuts.lean:19 | `XRk_CircleModel` |
| `XRm_ReverseSites.body_cursor` | evidence/extraction-assoc5-20261027/XRm_ReverseSites.lean:12 | `XRk_ByteFields` |
| `XRm_ReverseSites.cursor_zero` | evidence/extraction-assoc5-20261027/XRm_ReverseSites.lean:36 | `XRk_ByteFields` |
| `XRm_ReverseSites.reverse_site` | evidence/extraction-assoc5-20261027/XRm_ReverseSites.lean:45 | `XRk_ByteFields` |
| `XRm_ReverseSites.caller_prefix` | evidence/extraction-assoc5-20261027/XRm_ReverseSites.lean:52 | `XRk_ByteFields` |
| `XRm_ReverseSites.nonvacuity` | evidence/extraction-assoc5-20261027/XRm_ReverseSites.lean:59 | `XRk_ByteFields` |
| `XRm_Reverse.cursor` | evidence/extraction-assoc5-20261027/XRm_ReverseStep.lean:5 | `XRk_ByteFields` |
| `XRm_TableBlock.append` | evidence/extraction-assoc5-20261027/XRm_TableBlock.lean:7 | `XRk_CircleModel` |
| `XRm_TableBlock.first` | evidence/extraction-assoc5-20261027/XRm_TableBlock.lean:12 | `XRk_CircleModel` |
| `XRm_TableBounds.A0` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:5 | `XRk_CircleModel` |
| `XRm_TableBounds.A1` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:11 | `XRk_CircleModel` |
| `XRm_TableBounds.A2` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:17 | `XRk_CircleModel` |
| `XRm_TableBounds.A3` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:23 | `XRk_CircleModel` |
| `XRm_TableBounds.A4` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:29 | `XRk_CircleModel` |
| `XRm_TableBounds.A5` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:35 | `XRk_CircleModel` |
| `XRm_TableBounds.A6` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:41 | `XRk_CircleModel` |
| `XRm_TableBounds.A7` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:47 | `XRk_CircleModel` |
| `XRm_TableBounds.A8` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:53 | `XRk_CircleModel` |
| `XRm_TableBounds.A9` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:59 | `XRk_CircleModel` |
| `XRm_TableBounds.A10` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:65 | `XRk_CircleModel` |
| `XRm_TableBounds.A11` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:71 | `XRk_CircleModel` |
| `XRm_TableBounds.A12` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:77 | `XRk_CircleModel` |
| `XRm_TableBounds.A13` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:83 | `XRk_CircleModel` |
| `XRm_TableBounds.A14` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:89 | `XRk_CircleModel` |
| `XRm_TableBounds.A15` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:95 | `XRk_CircleModel` |
| `XRm_TableBounds.tableA` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:101 | `XRk_CircleModel` |
| `XRm_TableBounds.B0` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:105 | `XRk_CircleModel` |
| `XRm_TableBounds.B1` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:111 | `XRk_CircleModel` |
| `XRm_TableBounds.B2` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:117 | `XRk_CircleModel` |
| `XRm_TableBounds.B3` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:123 | `XRk_CircleModel` |
| `XRm_TableBounds.B4` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:129 | `XRk_CircleModel` |
| `XRm_TableBounds.B5` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:135 | `XRk_CircleModel` |
| `XRm_TableBounds.B6` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:141 | `XRk_CircleModel` |
| `XRm_TableBounds.B7` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:147 | `XRk_CircleModel` |
| `XRm_TableBounds.B8` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:153 | `XRk_CircleModel` |
| `XRm_TableBounds.B9` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:159 | `XRk_CircleModel` |
| `XRm_TableBounds.B10` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:165 | `XRk_CircleModel` |
| `XRm_TableBounds.B11` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:171 | `XRk_CircleModel` |
| `XRm_TableBounds.B12` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:177 | `XRk_CircleModel` |
| `XRm_TableBounds.B13` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:183 | `XRk_CircleModel` |
| `XRm_TableBounds.B14` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:189 | `XRk_CircleModel` |
| `XRm_TableBounds.B15` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:195 | `XRk_CircleModel` |
| `XRm_TableBounds.tableB` | evidence/extraction-assoc5-20261027/XRm_TableBounds.lean:201 | `XRk_CircleModel` |
| `XRm_Tx1Cuts.cuts` | evidence/extraction-assoc5-20261027/XRm_Tx1Cuts.lean:8 | `XRk_CircleModel` |
| `XRm_VectorEffects.clone` | evidence/extraction-assoc5-20261027/XRm_VectorEffects.lean:7 | `XRk_CircleModel` |
| `XRm_VectorEffects.extend` | evidence/extraction-assoc5-20261027/XRm_VectorEffects.lean:13 | `XRk_CircleModel` |
| `XRm_VectorEffects.push` | evidence/extraction-assoc5-20261027/XRm_VectorEffects.lean:33 | `XRk_CircleModel` |
| `XRn_ClaimAssociation.part_rehash` | evidence/extraction-assoc6-20261027/XRn_ClaimAssociation.lean:13 | `XRk_CircleModel` |
| `XRn_ClaimAssociation.digest_irrelevant` | evidence/extraction-assoc6-20261027/XRn_ClaimAssociation.lean:17 | `XRk_CircleModel` |
| `XRn_ClaimAssociation.rehash_result` | evidence/extraction-assoc6-20261027/XRn_ClaimAssociation.lean:22 | `XRk_CircleModel` |
| `XRn_JoinedNonvacuity.rejected_initialization` | evidence/extraction-assoc6-20261027/XRn_JoinedAudit.lean:11 | `XRn_Join_TypesExternal` |
| `XRn_JoinedNonvacuity.accessor` | evidence/extraction-assoc6-20261027/XRn_JoinedAudit.lean:16 | `XRn_Join_TypesExternal` |
| `XRn_PreparedAssociation.same_run` | evidence/extraction-assoc6-20261027/XRn_PreparedAssociation.lean:10 | `XRk_CircleModel` |
| `XRn_PreparedBoundaries.legacy_claim_unused` | evidence/extraction-assoc6-20261027/XRn_PreparedBoundaries.lean:32 | `XRk_CircleModel` |
| `XRn_PreparedCuts.source` | evidence/extraction-assoc6-20261027/XRn_PreparedCuts.lean:8 | `XRk_CircleModel` |
| `XRn_PreparedScalars.scalar` | evidence/extraction-assoc6-20261027/XRn_PreparedScalars.lean:8 | `XRk_CircleModel` |
| `XRn_PreparedScalars.scalar_k` | evidence/extraction-assoc6-20261027/XRn_PreparedScalars.lean:27 | `XRk_CircleModel` |
| `XRn_QmSampler.div_body` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:30 | `XRk_CircleModel` |
| `XRn_QmSampler.div_loop` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:35 | `XRk_CircleModel` |
| `XRn_QmSampler.div_pass` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:42 | `XRk_CircleModel` |
| `XRn_QmSampler.digits0_body` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:46 | `XRk_CircleModel` |
| `XRn_QmSampler.digits0` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:49 | `XRk_CircleModel` |
| `XRn_QmSampler.digits1_body` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:52 | `XRk_CircleModel` |
| `XRn_QmSampler.digits1` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:57 | `XRk_CircleModel` |
| `XRn_QmSampler.digits` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:64 | `XRk_CircleModel` |
| `XRn_QmSampler.sample` | evidence/extraction-assoc6-20261027/XRn_QmSampler.lean:68 | `XRk_CircleModel` |
| `XRn_Transcript.tag` | evidence/extraction-assoc6-20261027/XRn_Transcript.lean:8 | `XRk_CircleModel` |
| `XRn_Transcript.folds` | evidence/extraction-assoc6-20261027/XRn_Transcript.lean:12 | `XRk_CircleModel` |
| `XRn_Transcript.start` | evidence/extraction-assoc6-20261027/XRn_Transcript.lean:16 | `XRk_CircleModel` |
| `XRn_TranscriptBlock.absorb` | evidence/extraction-assoc6-20261027/XRn_TranscriptBlock.lean:8 | `XRk_CircleModel` |
| `XRn_TranscriptBlock.block` | evidence/extraction-assoc6-20261027/XRn_TranscriptBlock.lean:15 | `XRk_CircleModel` |
| `XRo_Join_Nonvacuity.rejected_initialization` | evidence/extraction-assoc7-20261027/XRo_Join_Nonvacuity.lean:11 | `XRo_Join_Nonvacuity` |
| `XRo_Join_PowersAssociation.powers` | evidence/extraction-assoc7-20261027/XRo_Join_PowersAssociation.lean:6 | `XRo_Join_PowersLoop` |
| `XRo_Join_PowersLoop.suffix` | evidence/extraction-assoc7-20261027/XRo_Join_PowersLoop.lean:10 | `XRo_Join_PowersLoop` |
| `XRo_Join_PreparedAssociation.same_run` | evidence/extraction-assoc7-20261027/XRo_Join_PreparedAssociation.lean:10 | `XRn_Join_TypesExternal` |
| `XRo_Join_PreparedCuts.source` | evidence/extraction-assoc7-20261027/XRo_Join_PreparedCuts.lean:8 | `XRn_Join_TypesExternal` |
| `XRo_Join_TranscriptState.state` | evidence/extraction-assoc7-20261027/XRo_Join_TranscriptState.lean:7 | `XRo_Join_Installed` |
| `XRp_DivisionObstruction.ranks_differ` | evidence/extraction-assoc8-20261027/XRp_DivisionObstruction.lean:14 | `XRn_Join_TypesExternal` |
| `XRp_DivisionObstruction.division_commutation_false` | evidence/extraction-assoc8-20261027/XRp_DivisionObstruction.lean:21 | `XRn_Join_TypesExternal` |
| `XRp_DivisionObstruction.nonvacuity` | evidence/extraction-assoc8-20261027/XRp_DivisionObstruction.lean:28 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero2` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:10 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero3` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:23 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero4` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:36 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero5` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:49 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero6` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:62 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero7` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:75 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.zero8` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:88 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.stop` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:101 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.trace` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:104 | `XRn_Join_TypesExternal` |
| `XRp_IndexedTrace.indexed` | evidence/extraction-assoc8-20261027/XRp_IndexedTrace.lean:115 | `XRn_Join_TypesExternal` |
| `XRp_IndexedWitness.writes_quotient` | evidence/extraction-assoc8-20261027/XRp_IndexedWitness.lean:9 | `XRn_Join_TypesExternal` |
| `XRp_LoopReplay.sound` | evidence/extraction-assoc8-20261027/XRp_LoopReplay.lean:14 | `XRn_Join_ABI` |
| `XRp_PowersNonvacuity.canonical` | evidence/extraction-assoc8-20261027/XRp_PowersNonvacuity.lean:9 | `XRo_Join_Installed` |
| `XRp_PowersNonvacuity.source_zero` | evidence/extraction-assoc8-20261027/XRp_PowersNonvacuity.lean:13 | `XRo_Join_Installed` |
| `XRp_PowersNonvacuity.both_succeed` | evidence/extraction-assoc8-20261027/XRp_PowersNonvacuity.lean:18 | `XRo_Join_Installed` |
| `XRr_QueryFrame.guard` | evidence/extraction-assoc10-20261027/XRr_QueryFrame.lean:25 | `XRn_Join_TypesExternal` |
| `XRy_ArrayMap.set` | evidence/extraction-assoc17-20261027/XRy_ArrayMap.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ArrayMap.repeated` | evidence/extraction-assoc17-20261027/XRy_ArrayMap.lean:13 | `XRn_Join_QueryModel` |
| `XRy_ArrayRead.read` | evidence/extraction-assoc17-20261027/XRy_ArrayRead.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ArrayRead.mapped` | evidence/extraction-assoc17-20261027/XRy_ArrayRead.lean:13 | `XRn_Join_QueryModel` |
| `XRy_ArrayRead.usize_small` | evidence/extraction-assoc17-20261027/XRy_ArrayRead.lean:18 | `XRn_Join_QueryModel` |
| `XRy_ClaimAdd.full_graph` | evidence/extraction-assoc17-20261027/XRy_ClaimAdd.lean:13 | `XRn_Join_QueryModel` |
| `XRy_ClaimAdd.graph` | evidence/extraction-assoc17-20261027/XRy_ClaimAdd.lean:22 | `XRn_Join_QueryModel` |
| `XRy_ClaimAdd.add` | evidence/extraction-assoc17-20261027/XRy_ClaimAdd.lean:29 | `XRn_Join_QueryModel` |
| `XRy_ClaimArithmetic.roundtrip` | evidence/extraction-assoc17-20261027/XRy_ClaimArithmetic.lean:16 | `XRn_Join_QueryModel` |
| `XRy_ClaimArithmetic.injective` | evidence/extraction-assoc17-20261027/XRy_ClaimArithmetic.lean:18 | `XRn_Join_QueryModel` |
| `XRy_ClaimArithmetic.mul_graph` | evidence/extraction-assoc17-20261027/XRy_ClaimArithmetic.lean:22 | `XRn_Join_QueryModel` |
| `XRy_ClaimArithmetic.multiply` | evidence/extraction-assoc17-20261027/XRy_ClaimArithmetic.lean:29 | `XRn_Join_QueryModel` |
| `XRy_ClaimFold.fold` | evidence/extraction-assoc17-20261027/XRy_ClaimFold.lean:10 | `XRn_Join_QueryModel` |
| `XRy_ClaimPartFactor.factor` | evidence/extraction-assoc17-20261027/XRy_ClaimPartFactor.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ClaimSelect.usize_value` | evidence/extraction-assoc17-20261027/XRy_ClaimSelect.lean:8 | `XRn_Join_QueryModel` |
| `XRy_ClaimSelectClaims.claims` | evidence/extraction-assoc17-20261027/XRy_ClaimSelectClaims.lean:8 | `XRn_Join_QueryModel` |
| `XRy_ClaimSelectExtra.extra` | evidence/extraction-assoc17-20261027/XRy_ClaimSelectExtra.lean:8 | `XRn_Join_QueryModel` |
| `XRy_ClaimSelectExtra.before_z1` | evidence/extraction-assoc17-20261027/XRy_ClaimSelectExtra.lean:25 | `XRn_Join_QueryModel` |
| `XRy_ClaimSum.zero_canonical` | evidence/extraction-assoc17-20261027/XRy_ClaimSum.lean:8 | `XRn_Join_QueryModel` |
| `XRy_ClaimSum.zero_claim` | evidence/extraction-assoc17-20261027/XRy_ClaimSum.lean:11 | `XRn_Join_QueryModel` |
| `XRy_ClaimSum.sum` | evidence/extraction-assoc17-20261027/XRy_ClaimSum.lean:17 | `XRn_Join_QueryModel` |
| `XRy_ClaimSumLoop.paired` | evidence/extraction-assoc17-20261027/XRy_ClaimSumLoop.lean:15 | `XRn_Join_QueryModel` |
| `XRy_ClaimSumStep.paired` | evidence/extraction-assoc17-20261027/XRy_ClaimSumStep.lean:19 | `XRn_Join_QueryModel` |
| `XRy_ComplexCanonical.of_map_ok` | evidence/extraction-assoc17-20261027/XRy_ComplexCanonical.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ComplexCanonical.mul` | evidence/extraction-assoc17-20261027/XRy_ComplexCanonical.lean:14 | `XRn_Join_QueryModel` |
| `XRy_ComplexCanonical.add` | evidence/extraction-assoc17-20261027/XRy_ComplexCanonical.lean:25 | `XRn_Join_QueryModel` |
| `XRy_ComplexCanonical.sub` | evidence/extraction-assoc17-20261027/XRy_ComplexCanonical.lean:36 | `XRn_Join_QueryModel` |
| `XRy_ComplexMultiply.graph` | evidence/extraction-assoc17-20261027/XRy_ComplexMultiply.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ComplexMultiply.multiply` | evidence/extraction-assoc17-20261027/XRy_ComplexMultiply.lean:20 | `XRn_Join_QueryModel` |
| `XRy_Cross64.sum_value` | evidence/extraction-assoc17-20261027/XRy_Cross64.lean:8 | `XRn_Join_QueryModel` |
| `XRy_Cross64.fragment` | evidence/extraction-assoc17-20261027/XRy_Cross64.lean:20 | `XRn_Join_QueryModel` |
| `XRy_IndexedSum.run_fold` | evidence/extraction-assoc17-20261027/XRy_IndexedSum.lean:7 | `XRn_Join_QueryModel` |
| `XRy_ListPowers.total` | evidence/extraction-assoc17-20261027/XRy_ListPowers.lean:7 | `XRn_Join_QueryModel` |
| `XRy_LoopWide.canonical` | evidence/extraction-assoc17-20261027/XRy_LoopWide.lean:12 | `XRn_Join_QueryModel` |
| `XRy_LoopWide.multiply` | evidence/extraction-assoc17-20261027/XRy_LoopWide.lean:15 | `XRn_Join_QueryModel` |
| `XRy_MulByR.total` | evidence/extraction-assoc17-20261027/XRy_MulByR.lean:7 | `XRn_Join_QueryModel` |
| `XRy_MulByR.same` | evidence/extraction-assoc17-20261027/XRy_MulByR.lean:28 | `XRn_Join_QueryModel` |
| `XRy_NarrowPrepare.emitted` | evidence/extraction-assoc17-20261027/XRy_NarrowPrepare.lean:131 | `XRn_Join_QueryModel` |
| `XRy_NarrowPrepare.gamma_canonical` | evidence/extraction-assoc17-20261027/XRy_NarrowPrepare.lean:135 | `XRn_Join_QueryModel` |
| `XRy_Powers.one_canonical` | evidence/extraction-assoc17-20261027/XRy_Powers.lean:10 | `XRn_Join_QueryModel` |
| `XRy_Powers.zero_loop` | evidence/extraction-assoc17-20261027/XRy_Powers.lean:13 | `XRn_Join_QueryModel` |
| `XRy_Powers.one_loop` | evidence/extraction-assoc17-20261027/XRy_Powers.lean:17 | `XRn_Join_QueryModel` |
| `XRy_Powers.paired` | evidence/extraction-assoc17-20261027/XRy_Powers.lean:22 | `XRn_Join_QueryModel` |
| `XRy_PowersLoop.done` | evidence/extraction-assoc17-20261027/XRy_PowersLoop.lean:7 | `XRn_Join_QueryModel` |
| `XRy_PowersLoop.cont` | evidence/extraction-assoc17-20261027/XRy_PowersLoop.lean:10 | `XRn_Join_QueryModel` |
| `XRy_PowersLoop.paired` | evidence/extraction-assoc17-20261027/XRy_PowersLoop.lean:13 | `XRn_Join_QueryModel` |
| `XRy_PowersPublic.roundtrip` | evidence/extraction-assoc17-20261027/XRy_PowersPublic.lean:8 | `XRn_Join_QueryModel` |
| `XRy_PowersPublic.powers` | evidence/extraction-assoc17-20261027/XRy_PowersPublic.lean:16 | `XRn_Join_QueryModel` |
| `XRy_PowersStep.mutable` | evidence/extraction-assoc17-20261027/XRy_PowersStep.lean:7 | `XRn_Join_QueryModel` |
| `XRy_PowersStep.step` | evidence/extraction-assoc17-20261027/XRy_PowersStep.lean:16 | `XRn_Join_QueryModel` |
| `XRy_PrepareCallbacks.scalar` | evidence/extraction-assoc17-20261027/XRy_PrepareCallbacks.lean:8 | `XRn_Join_QueryModel` |
| `XRy_PrepareCallbacks.queries` | evidence/extraction-assoc17-20261027/XRy_PrepareCallbacks.lean:17 | `XRn_Join_QueryModel` |
| `XRy_PrepareCallbacks.scalar_k` | evidence/extraction-assoc17-20261027/XRy_PrepareCallbacks.lean:23 | `XRn_Join_QueryModel` |
| `XRy_PrepareCallbacks.state` | evidence/extraction-assoc17-20261027/XRy_PrepareCallbacks.lean:30 | `XRn_Join_QueryModel` |
| `XRy_PreparePowers.gamma_canonical` | evidence/extraction-assoc17-20261027/XRy_PreparePowers.lean:13 | `XRn_Join_QueryModel` |
| `XRy_PreparePowers.change_powers` | evidence/extraction-assoc17-20261027/XRy_PreparePowers.lean:20 | `XRn_Join_QueryModel` |
| `XRy_PreparePowers.prepare` | evidence/extraction-assoc17-20261027/XRy_PreparePowers.lean:37 | `XRn_Join_QueryModel` |
| `XRy_PrepareRawScratch.prepare` | evidence/extraction-assoc17-20261027/XRy_PrepareRawScratch.lean:13 | `XRn_Join_QueryModel` |
| `XRy_QmLinear.add` | evidence/extraction-assoc17-20261027/XRy_QmLinear.lean:7 | `XRn_Join_QueryModel` |
| `XRy_QmLinear.sub` | evidence/extraction-assoc17-20261027/XRy_QmLinear.lean:17 | `XRn_Join_QueryModel` |
| `XRy_QmLinear.mul_u_total` | evidence/extraction-assoc17-20261027/XRy_QmLinear.lean:26 | `XRn_Join_QueryModel` |
| `XRy_QmLinear.mul_u` | evidence/extraction-assoc17-20261027/XRy_QmLinear.lean:38 | `XRn_Join_QueryModel` |
| `XRy_QmMultiply.total` | evidence/extraction-assoc17-20261027/XRy_QmMultiply.lean:7 | `XRn_Join_QueryModel` |
| `XRy_QmMultiply.multiply` | evidence/extraction-assoc17-20261027/XRy_QmMultiply.lean:23 | `XRn_Join_QueryModel` |
| `XRy_Queries.boundaries` | evidence/extraction-assoc17-20261027/XRy_Queries.lean:8 | `XRn_Join_QueryModel` |
| `XRy_Queries.queries` | evidence/extraction-assoc17-20261027/XRy_Queries.lean:18 | `XRn_Join_QueryModel` |
| `XRy_QueryEmbedding.embed` | evidence/extraction-assoc17-20261027/XRy_QueryEmbedding.lean:8 | `XRn_Join_QueryModel` |
| `XRy_QueryLaws.decode` | evidence/extraction-assoc17-20261027/XRy_QueryLaws.lean:21 | `XRn_Join_QueryModel` |
| `XRy_QueryTransport.bind_cont` | evidence/extraction-assoc17-20261027/XRy_QueryTransport.lean:8 | `XRn_Join_QueryModel` |
| `XRy_QueryTransport.raw` | evidence/extraction-assoc17-20261027/XRy_QueryTransport.lean:15 | `XRn_Join_QueryModel` |
| `XRy_Reducer64.reducer` | evidence/extraction-assoc17-20261027/XRy_Reducer64.lean:8 | `XRn_Join_QueryModel` |
| `XRy_Reducer64.add64` | evidence/extraction-assoc17-20261027/XRy_Reducer64.lean:16 | `XRn_Join_QueryModel` |
| `XRy_Reducer64.mul64` | evidence/extraction-assoc17-20261027/XRy_Reducer64.lean:26 | `XRn_Join_QueryModel` |
| `XRy_Remainder.canonical` | evidence/extraction-assoc17-20261027/XRy_Remainder.lean:6 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.finish_same` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:27 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.fold_same` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:78 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.guarded_step` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:100 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.raw_unrolled` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:107 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.run_unrolled` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:120 | `XRn_Join_QueryModel` |
| `XRy_WholeDriver.whole` | evidence/extraction-assoc17-20261027/XRy_WholeDriver.lean:171 | `XRn_Join_QueryModel` |
| `XRy_WideMultiply.total` | evidence/extraction-assoc17-20261027/XRy_WideMultiply.lean:11 | `XRn_Join_QueryModel` |
| `XRy_WideMultiply.multiply` | evidence/extraction-assoc17-20261027/XRy_WideMultiply.lean:29 | `XRn_Join_QueryModel` |
| `XSa_ArrayPrefix.write` | evidence/extraction-assoc19-20261027/XSa_ArrayPrefix.lean:6 | `XRn_Join_QueryModel` |
| `XSa_ArrayPrefix.last` | evidence/extraction-assoc19-20261027/XSa_ArrayPrefix.lean:13 | `XRn_Join_QueryModel` |
| `XSa_ArraySeven.update` | evidence/extraction-assoc19-20261027/XSa_ArraySeven.lean:8 | `XRn_Join_QueryModel` |
| `XSa_ArraySeven.canonical_set` | evidence/extraction-assoc19-20261027/XSa_ArraySeven.lean:13 | `XRn_Join_QueryModel` |
| `XSa_CachedClaim.claim` | evidence/extraction-assoc19-20261027/XSa_CachedClaim.lean:15 | `XRn_Join_QueryModel` |
| `XSa_CheckedQ.checked` | evidence/extraction-assoc19-20261027/XSa_CheckedQ.lean:15 | `XRn_Join_QueryModel` |
| `XSa_ClaimDot.dot` | evidence/extraction-assoc19-20261027/XSa_ClaimDot.lean:8 | `XRn_Join_QueryModel` |
| `XSa_ClaimInitial.front` | evidence/extraction-assoc19-20261027/XSa_ClaimInitial.lean:10 | `XRn_Join_QueryModel` |
| `XSa_ClaimInitial.canonical` | evidence/extraction-assoc19-20261027/XSa_ClaimInitial.lean:13 | `XRn_Join_QueryModel` |
| `XSa_ClaimInitial.actual` | evidence/extraction-assoc19-20261027/XSa_ClaimInitial.lean:21 | `XRn_Join_QueryModel` |
| `XSa_ClaimPairs.pairs` | evidence/extraction-assoc19-20261027/XSa_ClaimPairs.lean:13 | `XRn_Join_QueryModel` |
| `XSa_ClaimPairs.step` | evidence/extraction-assoc19-20261027/XSa_ClaimPairs.lean:16 | `XRn_Join_QueryModel` |
| `XSa_ClaimRaw.factor` | evidence/extraction-assoc19-20261027/XSa_ClaimRaw.lean:9 | `XRn_Join_QueryModel` |
| `XSa_ClaimSelect.all_six` | evidence/extraction-assoc19-20261027/XSa_ClaimSelect.lean:8 | `XRn_Join_QueryModel` |
| `XSa_ClaimSumJoin.fold` | evidence/extraction-assoc19-20261027/XSa_ClaimSumJoin.lean:9 | `XRn_Join_QueryModel` |
| `XSa_ClaimSumJoin.paired` | evidence/extraction-assoc19-20261027/XSa_ClaimSumJoin.lean:19 | `XRn_Join_QueryModel` |
| `XSa_ClaimY1.raw` | evidence/extraction-assoc19-20261027/XSa_ClaimY1.lean:8 | `XRn_Join_QueryModel` |
| `XSa_ClaimY1.sixth` | evidence/extraction-assoc19-20261027/XSa_ClaimY1.lean:21 | `XRn_Join_QueryModel` |
| `XSa_DotActual.push` | evidence/extraction-assoc19-20261027/XSa_DotActual.lean:7 | `XRn_Join_QueryModel` |
| `XSa_DotBody.body` | evidence/extraction-assoc19-20261027/XSa_DotBody.lean:8 | `XRn_Join_QueryModel` |
| `XSa_DotCarriers.new_dot` | evidence/extraction-assoc19-20261027/XSa_DotCarriers.lean:13 | `XRn_Join_QueryModel` |
| `XSa_DotCarriers.parser` | evidence/extraction-assoc19-20261027/XSa_DotCarriers.lean:16 | `XRn_Join_QueryModel` |
| `XSa_DotControl.push` | evidence/extraction-assoc19-20261027/XSa_DotControl.lean:8 | `XRn_Join_QueryModel` |
| `XSa_DotDone.done` | evidence/extraction-assoc19-20261027/XSa_DotDone.lean:8 | `XRn_Join_QueryModel` |
| `XSa_DotLoop.paired` | evidence/extraction-assoc19-20261027/XSa_DotLoop.lean:9 | `XRn_Join_QueryModel` |
| `XSa_DotModel.model` | evidence/extraction-assoc19-20261027/XSa_DotModel.lean:7 | `XRn_Join_QueryModel` |
| `XSa_DotPushPair.paired` | evidence/extraction-assoc19-20261027/XSa_DotPushPair.lean:9 | `XRn_Join_QueryModel` |
| `XSa_DotReject.reject` | evidence/extraction-assoc19-20261027/XSa_DotReject.lean:8 | `XRn_Join_QueryModel` |
| `XSa_DotRun.coefficient` | evidence/extraction-assoc19-20261027/XSa_DotRun.lean:32 | `XRn_Join_QueryModel` |
| `XSa_DotWord.update` | evidence/extraction-assoc19-20261027/XSa_DotWord.lean:6 | `XRn_Join_QueryModel` |
| `XSa_FinishFour.four` | evidence/extraction-assoc19-20261027/XSa_FinishFour.lean:7 | `XRn_Join_QueryModel` |
| `XSa_FinishPair.paired` | evidence/extraction-assoc19-20261027/XSa_FinishPair.lean:14 | `XRn_Join_QueryModel` |
| `XSa_FinishWord.reduce` | evidence/extraction-assoc19-20261027/XSa_FinishWord.lean:6 | `XRn_Join_QueryModel` |
| `XSa_FoldCongr.fold` | evidence/extraction-assoc19-20261027/XSa_FoldCongr.lean:6 | `XRn_Join_QueryModel` |
| `XSa_GenericPairs.fold_map` | evidence/extraction-assoc19-20261027/XSa_GenericPairs.lean:7 | `XRn_Join_QueryModel` |
| `XSa_GenericPairs.indexed_zip` | evidence/extraction-assoc19-20261027/XSa_GenericPairs.lean:19 | `XRn_Join_QueryModel` |
| `XSa_ListClaimRaw.factor` | evidence/extraction-assoc19-20261027/XSa_ListClaimRaw.lean:17 | `XRn_Join_QueryModel` |
| `XSa_LoopErrors.failed` | evidence/extraction-assoc19-20261027/XSa_LoopErrors.lean:6 | `XRn_Join_QueryModel` |
| `XSa_LoopErrors.diverged` | evidence/extraction-assoc19-20261027/XSa_LoopErrors.lean:9 | `XRn_Join_QueryModel` |
| `XSa_OptionFold.none_fold` | evidence/extraction-assoc19-20261027/XSa_OptionFold.lean:18 | `XRn_Join_QueryModel` |
| `XSa_OptionFold.same` | evidence/extraction-assoc19-20261027/XSa_OptionFold.lean:24 | `XRn_Join_QueryModel` |
| `XSa_ParserBytes.words` | evidence/extraction-assoc19-20261027/XSa_ParserBytes.lean:12 | `XRn_Join_QueryModel` |
| `XSa_ParserFixed.fixed` | evidence/extraction-assoc19-20261027/XSa_ParserFixed.lean:8 | `XRn_Join_QueryModel` |
| `XSa_ParserLane.lane` | evidence/extraction-assoc19-20261027/XSa_ParserLane.lean:15 | `XRn_Join_QueryModel` |
| `XSa_ParserRange.range` | evidence/extraction-assoc19-20261027/XSa_ParserRange.lean:6 | `XRn_Join_QueryModel` |
| `XSa_ParserTotal.bytes` | evidence/extraction-assoc19-20261027/XSa_ParserTotal.lean:7 | `XRn_Join_QueryModel` |
| `XSa_ParserWords.word` | evidence/extraction-assoc19-20261027/XSa_ParserWords.lean:8 | `XRn_Join_QueryModel` |
| `XSa_PartAssociation.part` | evidence/extraction-assoc19-20261027/XSa_PartAssociation.lean:8 | `XRn_Join_QueryModel` |
| `XSa_PartCanonical.canonical` | evidence/extraction-assoc19-20261027/XSa_PartCanonical.lean:8 | `XRn_Join_QueryModel` |
| `XSa_PartFold.same_step` | evidence/extraction-assoc19-20261027/XSa_PartFold.lean:35 | `XRn_Join_QueryModel` |
| `XSa_PartFold.factor` | evidence/extraction-assoc19-20261027/XSa_PartFold.lean:47 | `XRn_Join_QueryModel` |
| `XSa_PartRun.run` | evidence/extraction-assoc19-20261027/XSa_PartRun.lean:7 | `XRn_Join_QueryModel` |
| `XSa_PointBody.body` | evidence/extraction-assoc19-20261027/XSa_PointBody.lean:8 | `XRn_Join_QueryModel` |
| `XSa_PointList.paired` | evidence/extraction-assoc19-20261027/XSa_PointList.lean:20 | `XRn_Join_QueryModel` |
| `XSa_PointLoop.paired` | evidence/extraction-assoc19-20261027/XSa_PointLoop.lean:9 | `XRn_Join_QueryModel` |
| `XSa_PointRun.done` | evidence/extraction-assoc19-20261027/XSa_PointRun.lean:23 | `XRn_Join_QueryModel` |
| `XSa_PowersArray.powers` | evidence/extraction-assoc19-20261027/XSa_PowersArray.lean:8 | `XRn_Join_QueryModel` |
| `XSa_PowersDimensions.seven` | evidence/extraction-assoc19-20261027/XSa_PowersDimensions.lean:9 | `XRn_Join_QueryModel` |
| `XSa_PowersDimensions.twenty_nine` | evidence/extraction-assoc19-20261027/XSa_PowersDimensions.lean:18 | `XRn_Join_QueryModel` |
| `XSa_PowersList.paired` | evidence/extraction-assoc19-20261027/XSa_PowersList.lean:7 | `XRn_Join_QueryModel` |
| `XSa_PowersStep.last` | evidence/extraction-assoc19-20261027/XSa_PowersStep.lean:7 | `XRn_Join_QueryModel` |
| `XSa_PowersStep.next` | evidence/extraction-assoc19-20261027/XSa_PowersStep.lean:17 | `XRn_Join_QueryModel` |
| `XSa_QRawTotal.total` | evidence/extraction-assoc19-20261027/XSa_QRawTotal.lean:12 | `XRn_Join_QueryModel` |
| `XSa_RawActual.bound` | evidence/extraction-assoc19-20261027/XSa_RawActual.lean:7 | `XRn_Join_QueryModel` |
| `XSa_RawActual.actual` | evidence/extraction-assoc19-20261027/XSa_RawActual.lean:12 | `XRn_Join_QueryModel` |
| `XSa_RawFolds.uv` | evidence/extraction-assoc19-20261027/XSa_RawFolds.lean:6 | `XRn_Join_QueryModel` |
| `XSa_RawModel.model` | evidence/extraction-assoc19-20261027/XSa_RawModel.lean:8 | `XRn_Join_QueryModel` |
| `XSa_RawWrap.wrap` | evidence/extraction-assoc19-20261027/XSa_RawWrap.lean:6 | `XRn_Join_QueryModel` |
| `XSa_RawWrap.sub` | evidence/extraction-assoc19-20261027/XSa_RawWrap.lean:9 | `XRn_Join_QueryModel` |
| `XSa_RawWrap.fold_word` | evidence/extraction-assoc19-20261027/XSa_RawWrap.lean:15 | `XRn_Join_QueryModel` |
| `XSc_AccumulateCuts.source` | evidence/extraction-assoc21-20261027/XSc_AccumulateCuts.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_AccumulateFrame.source` | evidence/extraction-assoc21-20261027/XSc_AccumulateFrame.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_FinishRestore.source` | evidence/extraction-assoc21-20261027/XSc_FinishRestore.lean:6 | `XRn_Join_TypesExternal` |
| `XSc_GammaAssociation.sampler` | evidence/extraction-assoc21-20261027/XSc_GammaAssociation.lean:8 | `XRo_Join_OrdinaryDecode` |
| `XSc_GammaAssociation.scalar` | evidence/extraction-assoc21-20261027/XSc_GammaAssociation.lean:13 | `XRo_Join_OrdinaryDecode` |
| `XSc_HybridCheckpointShape.source` | evidence/extraction-assoc21-20261027/XSc_HybridCheckpointShape.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_HybridMaterialized.source` | evidence/extraction-assoc21-20261027/XSc_HybridMaterialized.lean:9 | `XRn_Join_TypesExternal` |
| `XSc_HybridPending64.source` | evidence/extraction-assoc21-20261027/XSc_HybridPending64.lean:10 | `XRn_Join_TypesExternal` |
| `XSc_LocalNonvacuity.rejected_parser` | evidence/extraction-assoc21-20261027/XSc_LocalNonvacuity.lean:9 | `XRo_Join_Carriers` |
| `XSc_LocalNonvacuity.decoder_total` | evidence/extraction-assoc21-20261027/XSc_LocalNonvacuity.lean:15 | `XRo_Join_Carriers` |
| `XSc_ParseDriver.source` | evidence/extraction-assoc21-20261027/XSc_ParseDriver.lean:8 | `XRo_Join_Carriers` |
| `XSc_ParseReconstruction.source` | evidence/extraction-assoc21-20261027/XSc_ParseReconstruction.lean:15 | `XRo_Join_Carriers` |
| `XSc_ParseResume.advance` | evidence/extraction-assoc21-20261027/XSc_ParseResume.lean:12 | `XRo_Join_Carriers` |
| `XSc_ParseStage00.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage00.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage01.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage01.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage02.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage02.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage03.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage03.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage04.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage04.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage05.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage05.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage06.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage06.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage07.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage07.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage08.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage08.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage09.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage09.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage10.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage10.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage11.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage11.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage12.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage12.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage13.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage13.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage14.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage14.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage15.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage15.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage16.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage16.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage17.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage17.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage18.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage18.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage19.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage19.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage20.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage20.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage21.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage21.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage22.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage22.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage23.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage23.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage24.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage24.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage25.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage25.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage26.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage26.lean:6 | `XRo_Join_Carriers` |
| `XSc_ParseStage27.source` | evidence/extraction-assoc21-20261027/XSc_ParseStage27.lean:6 | `XRo_Join_Carriers` |
| `XSc_PushFrame.source` | evidence/extraction-assoc21-20261027/XSc_PushFrame.lean:7 | `XRn_Join_TypesExternal` |
| `XSc_PushLoopFrame.source` | evidence/extraction-assoc21-20261027/XSc_PushLoopFrame.lean:10 | `XRn_Join_TypesExternal` |
| `XSc_QueryCuts.source` | evidence/extraction-assoc21-20261027/XSc_QueryCuts.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_QueryDestination.source` | evidence/extraction-assoc21-20261027/XSc_QueryDestination.lean:9 | `XRn_Join_TypesExternal` |
| `XSc_QueryNext.bound` | evidence/extraction-assoc21-20261027/XSc_QueryNext.lean:5 | `XRn_Join_TypesExternal` |
| `XSc_QueryNext.source` | evidence/extraction-assoc21-20261027/XSc_QueryNext.lean:19 | `XRn_Join_TypesExternal` |
| `XSc_QueryPath.source` | evidence/extraction-assoc21-20261027/XSc_QueryPath.lean:24 | `XRn_Join_TypesExternal` |
| `XSc_QueryPendingFrame.source` | evidence/extraction-assoc21-20261027/XSc_QueryPendingFrame.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_QueryPendingReach.reached` | evidence/extraction-assoc21-20261027/XSc_QueryPendingReach.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_QueryPrefixIndex.reached` | evidence/extraction-assoc21-20261027/XSc_QueryPrefixIndex.lean:7 | `XRn_Join_TypesExternal` |
| `XSc_QueryTermCounter.source` | evidence/extraction-assoc21-20261027/XSc_QueryTermCounter.lean:7 | `XRn_Join_TypesExternal` |
| `XSc_QueryTermReach.reached` | evidence/extraction-assoc21-20261027/XSc_QueryTermReach.lean:8 | `XRn_Join_TypesExternal` |
| `XSc_QueryWeights.reached` | evidence/extraction-assoc21-20261027/XSc_QueryWeights.lean:6 | `XRn_Join_TypesExternal` |
| `XSc_RangeMeasure.terminal` | evidence/extraction-assoc21-20261027/XSc_RangeMeasure.lean:7 | `XRn_Join_TypesExternal` |
| `XSc_RangeMeasure.advance` | evidence/extraction-assoc21-20261027/XSc_RangeMeasure.lean:22 | `XRn_Join_TypesExternal` |
| `XSc_RecordByteLength.source` | evidence/extraction-assoc21-20261027/XSc_RecordByteLength.lean:10 | `XRo_Join_Carriers` |
| `XSc_RecordFieldArray.source` | evidence/extraction-assoc21-20261027/XSc_RecordFieldArray.lean:7 | `XRo_Join_Carriers` |
| `XSc_RecordFieldCarriers.limbs` | evidence/extraction-assoc21-20261027/XSc_RecordFieldCarriers.lean:13 | `XRo_Join_Carriers` |
| `XSc_RecordFieldGeneral.shape` | evidence/extraction-assoc21-20261027/XSc_RecordFieldGeneral.lean:7 | `XRo_Join_Carriers` |
| `XSc_RecordFieldGeneral.source` | evidence/extraction-assoc21-20261027/XSc_RecordFieldGeneral.lean:18 | `XRo_Join_Carriers` |
| `XSc_RecordFieldStep.rejected` | evidence/extraction-assoc21-20261027/XSc_RecordFieldStep.lean:11 | `XRo_Join_Carriers` |
| `XSc_RecordLimbs.source` | evidence/extraction-assoc21-20261027/XSc_RecordLimbs.lean:9 | `XRo_Join_Carriers` |
| `XSc_WordTransport.source` | evidence/extraction-assoc21-20261027/XSc_WordTransport.lean:6 | `XRo_Join_Carriers` |
