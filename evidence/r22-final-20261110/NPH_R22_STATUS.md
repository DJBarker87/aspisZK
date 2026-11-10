# NPH_ R22 status at 4bb3b3f (CheckedVsWrapping)

Job NPH_, 2026-11-10, branch codex/cx-r22-20261110 from research aceb08e73ed. Target not yet
established. This packet changes no ledger row, trust row, RSL, contract, merged module or
shipped source. It adds four Lean modules, the re-pinned cone table and receipts.

## 1. The obligation, re-pinned

The soundness theorems AspisR1.TAS_FinalB.deployed_splitB and deployed_charge are statements
about the gate's emitted bodies. 217 of the definitions those theorems reach have checked
bodies (Aeneas extraction with overflow checks ON: an overflow is an error result) and 8 mix
checked arithmetic with explicit wrapping_* calls (PCXD_R22_SPLIT.json, prov-p6r). The
deployed ELFs f8c0ec72… and 63ad3e9c… are built from 4bb3b3f with overflow checks OFF
(NOX_REALIZATION.md, trust line 8). In that build, integer + - * wrap and shifts mask their
amount.

The direction soundness needs is this one. If the deployed (wrapping) program accepts, then
the checked model accepts with the same result. Checked success inversion does not supply it.
R22TotalAcceptedPath already shows that an accepted wrapping run does not by itself give the
checked domain. The sufficient condition used here is the 2021 one, restated per definition at
4bb3b3f. Take every definition D in the deployed_splitB cone whose body class is CHECKED or
MIXED. One of the following must hold:

- (a) TOTAL. D's checked body returns ok on every input of its type. R22TotalCheckedComposition
  then makes every executed checked operation safe and the wrapping reading equal to the
  checked result.
- (b) PRECONDITION. D is total on a domain, and that domain is proved for every argument
  the reached callers pass.
- (c) DIRECT. Wrapping acceptance implies checked acceptance for D, proved directly.

The argument then runs by induction on execution order. Up to the first reached D, the two
semantics compute identical values. At D, (a) or (b) gives agreement, so the arguments of
the next D are the same in both semantics.

Re-pin rule. No 2021 judgment is carried over. The R22 packets pin b2727acd (R22-OVERFLOW)
and the R22-TOTAL audit base 6546eb41. Between b2727acd and 4bb3b3f, 31 frozen Rust files
under crates/ and programs/ change, among them fast_dots.rs, fast_pairing.rs, weights.rs,
r1_wire.rs, r1_pool_adapter.rs, pair_forest_trace.rs, pair_forest_terminal.rs and
poseidon2.rs. aspis-core field.rs and field/wide_exact.rs are unchanged. Every judgment below
is made fresh on the gate body in the L187 replayed closure. Only 13 of the 43 Lean source
files of the 2021 146-statement audit are still in the TAS_FinalB closure. The 2021 family
judgment appears in NPH_R22_CONE.json as information only (carried_over_from_2021 = false
everywhere).

The link from a gate body to 4bb3b3f is that definition's Stream C provenance status, and
this packet does not change it. The per-definition class supersedes NOX_'s module-level
split (24 checked, 2 wrapping, 71 undetermined modules).

## 2. Counts at 4bb3b3f

217 of the 225 CHECKED/MIXED definitions are in the replayed deployed_splitB REACHABLE list
(sha256 0b316cbb…0d30090), and the same 217 are in the deployed_charge list. The other 8 are in
neither raw cone. PCXD's set rule includes them because a CLOSED-row root reaches them:
BatchedWeights.push and push_loop.body (AspisR1BatchedWeightsExtraction and
S8Kani2MutableExtraction), finish_relation_round, NCV valid_sequences/zero_sequences loop
bodies, and NDH absorb_ref. They are kept in the obligation here because rows cite them.
Whether the headline needs them at all is a question for the cone owner.

| Judgment | Definitions | CLOSED rows they serve (union) |
|---|---:|---:|
| (a) TOTAL, proved by NPH_ | 60 (57 checked, 3 mixed) | 288 |
| (b) precondition proved from the callers | 0 | — |
| (c) direct | 0 | — |
| domain lemma proved, caller join open (not counted as (b)) | 28 | 228 |
| open | 137 (132 checked, 5 mixed) | 376 rows have at least one open or domain-only definition |

The checked and mixed definitions touch 396 CLOSED rows (PCXD_ROW_TABLES inverted). Only 20
of them are served exclusively by TOTAL definitions. The remaining 376 depend on at least one
definition that is not yet TOTAL.

TOTAL definitions:
- the 33 nullary usize layout constants in NHT_Constants, NJS_Extract, NMP_prepare, NMT_tx1,
  Op3I_Source, S1NativeCompactModelV1 and SelectedWideViewFunsV1;
- all 13 reduce_u64 copies;
- 9 M31.mul copies: the 5 frozen-shape copies and the 4 guarded-variant copies in
  AspisR72Sampler and the AspisV8R19 slices;
- the 3 wrapping-tail closure bodies of the mixed class (R72 r24 closure, and the
  AspisR1CanonicalQRawUnified and FIo_QRaw Q.raw closure_2);
- the 2 transition_kind decoders.

Domain lemmas: M31.add ×8, M31.sub ×7, M31.neg ×4, CM31.mul ×6, CM31.square ×3.

## 3. What is proved (standard axioms only, zero sorry)

The modules are compiled against the L187 replayed objects, with LEAN_PATH = own exports, then
codex-cx-replay-l187-20261109/objs, then base_ref, all by reference.

- **NPH_R22FieldRef.** Reference bodies refReduce, refAdd, refSub, refNeg and refMul, written
  statement for statement as the gate bodies of field.rs reduce_u64 31:0-44:1, M31::add/sub/
  neg/mul. Primitive success laws are re-stated, because R22TotalUnsignedPrimitives is not in
  the closure; a checked shift primitive is added.
  - Explicit operational trees reduceCode/addCode/subCode/negCode/mulCode, with checked_*Code
    proving that the checked semantics of each tree is the reference body. There is no
    Translation parameter.
  - Totality: refReduce_total and refMul_total for every input, with canonical output.
    refAdd_total and refSub_total for canonical limbs, and refNeg_total for limbs ≤ P, each
    with its residue equation.
  - R22 corollaries reduce_R22, mul_R22, add_R22, sub_R22, neg_R22: checked ok, NoOverflow
    of the tree, and wrapping of the tree = ok of the same value.
  - The obstruction add_noncanonical_fails: (2^32-1, 1) makes the checked add fail.
- **NPH_R22FieldCopies.** Each of the 37 frozen-shape kernel copies is definitionally equal to
  its reference (`funext; with_unfolding_all rfl` on structurally identical bodies; no large
  reduction), and inherits the R22 corollary. Also guarded M31.mul TOTAL ×4 and the 33 constants
  (each module's constant is definitionally the 2021 AspisR1Stage2 constant whose value
  R22Stage2LeafTotal proves).
- **NPH_R22CM31.** CM31.mul ×6 and CM31.square ×3 are checked-total on canonical limbs with
  canonical output. This includes R72's r23_product_u32_bounded helper in both branches. The
  module also proves the three closures and both transition_kind decoders TOTAL.
- **NPH_R22Weak.** The weak domain "limb ≤ P" is closed under every kernel above, and every
  checked operation on it succeeds: refAdd_weak, refSub_weak, CM31 *_weak, plus add/sub R22
  corollaries on it. sub_outside_weak_fails shows that a limb of 2^31+1 makes the first
  checked step of M31::sub overflow.

  The weak domain matters because frozen field.rs qm31_m31_dot builds `M31(x & P)` on its
  rejection path. That value can equal P. The comment there ("Keep arithmetic bounded even for
  a rejected encoding") matches this analysis.

The tree reading is precise. checked(tree) = gate body is proved in Lean. That wrapping(tree)
is what the SBF code computes is the P6/P7 interpretation (Aeneas translation fidelity and the
compiler trust lines of NOX_REALIZATION.md); Lean does not load the ELF. For the
guarded-M31.mul, closure, constant and transition_kind TOTAL results, only checked totality is
proved. Their wrapping agreement goes through extracted_total_R22 with that same P6
interpretation, as in 2021. The constants are Rust `const` items. rustc evaluates them at
compile time, where overflow is a hard error in either profile.

## 4. The remainder (T3)

Every open definition, with its reason and its exact row IDs, is in NPH_R22_CONE.json
(`nph_judgment`, `open_reason`, `rows`). By reason:

| Reason | Defs | Rows | Largest members (rows) | What closes it |
|---|---:|---:|---|---|
| Domain lemma proved, caller join open | 28 | 228 | SelectedMaskProbe M31.add (186), M31.sub (162), CM31.mul (156); CurrentWide/Qm31 copies (110–126) | Show that every limb entering a field kernel on the reached path is ≤ P. Sources: strict decoders (none for ≥ P), samplers (canonical), constants, the `& P` mask, kernel outputs. This is one invariant over the S1/S5/S8 caller lemmas already in the ledger domains. Estimate: 1–2 focused jobs, mostly composition. |
| Accumulator or cadence invariant not characterised | 32 | 140 | four_dots_one + loops (104, source changed), accumulate_batched_with_node (91), update_residue_row loops ×8 (86–91), Dot.push (39), BatchedWeights.push (22–24), finish loops (21–22), multiproof cone/sort (4–28) | Loop-invariant totality: term/phase counters, row width ≤ 256, once-per-row, w ≤ i < n ≤ 16. 2021 has numerical Kani/Lean bounds for single steps, not the loop induction. Estimate: the hardest residue, roughly one job per family (four_dots, residue/push, accumulate, multiproof). |
| Caller domain not composed | 100 | 215 | encode_digest_canonical_loop.body (67), digest_is_canonical ×2 (51, 32), pair-forest/Poseidon lane loops (24–38), weights.field (37), decode_k_value (31, source changed), samplers (16–27), parsers/readers (9–23), NCV/NCX reference loops (9–20) | Most need only "index < fixed array length" or "cursor + N ≤ len" from the immediate caller. digest_is_canonical and the NCV/NCX loops look total for every input once the Array/Slice length lemmas are applied. Readers and parsers need the 2021 cursor/length bounds composed with their actual callers. Estimate: 2–3 mechanical jobs. |
| Domain known, not composed | 2 | 37 | fibre_point (29), transport row_loop.body (24, mixed) | fibre_point: fibre-index admission bound (R17 tables, NNG_GeometryDomain094); ops.mul is a callback. row_loop: amounts ≤ 8 on iter.end ≤ 16 (PCQH-C5, NPE_). One small lemma each. |
| Existing domain lemma / same body | 2 | 123 | Q.raw ×2 (121 each, mixed) | AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs (in the closure) is canonical-limb totality for the Unified copy. FIo_QRaw has the identical normalised body (086b87d9e8e1e7cf) but distinct closure types, so the rfl transfer was not attempted. Both then need the limb join of row 1. The checked products in Q.raw are all of u32-widened limbs and small constants, so totality for every input is likely, given an Array.map value lemma. |
| No frozen counterpart | 1 | 27 | AspisR72Sampler r24_canonical_mul (mixed) | Provenance: replace it by a frozen-source extraction. R22 is moot until then. |

No tool limit was hit. Every failed compile was a proof-script error, recorded and changed
before the next attempt.

**Could the deployed binary accept where the checked model rejects, on a reachable path?**
This requires a checked operation on an accepted path to overflow while the wrapping program
continues and accepts. No such path was found, but for the 165 definitions that are not TOTAL
this is not proved. What is established is narrower.

1. On the 60 TOTAL definitions it cannot happen.
2. For the 28 field kernels it can happen only if a limb above P reaches them. Above 2^31,
   M31::sub, M31::neg and the CM31 cross products overflow (sub_outside_weak_fails,
   add_noncanonical_fails). Below that, every limb ≤ P is safe and the domain is closed.
3. A lexical scan of frozen 4bb3b3f crates/aspis-r1-cost-probe/src and aspis-core field.rs
   for direct `M31(` constructions finds, in non-test code, only kernel outputs, the checked
   constructor (line 244) and the `& P` mask (lines 1383–1384, value ≤ P, on an
   already-rejected encoding). This is a search, not a proof. It does not cover aspis-statement
   or crate-external constructions.

So no finding is reported, and no input is claimed. The open definitions' rows remain
exposed until (a), (b) or (c) is proved for them.

## 5. Proposed wording for the claim document (section 4.3, CheckedVsWrapping row)

> **CheckedVsWrapping (R22, OPEN).** The gate's emitted bodies for 217 reached definitions
> are checked translations (overflow is an error result), and 8 mix checked arithmetic with
> explicit wrapping_* calls. The deployed ELFs (f8c0ec72…, 63ad3e9c…, built from 4bb3b3f)
> wrap. The theorem transfers to the deployed binary when, for each of these 225 definitions,
> the checked body is total on every input (TOTAL), or total on a domain that the reached
> callers are proved to supply, or wrapping acceptance is proved to imply checked acceptance
> directly. R22TotalCheckedComposition then gives safety of every executed checked operation
> and equality of the wrapping and checked results, under the P6/P7 interpretation of the
> operational tree as the compiled code. Status at 4bb3b3f (NPH_,
> evidence/r22-final-20261110): 60 TOTAL (all reduce_u64 and M31.mul copies, the 33 layout
> constants, the 3 mixed-class closures, 2 decoders); 28 field kernels (M31 add/sub/neg,
> CM31 mul/square) are total on limbs ≤ P, a domain closed under every kernel, with the
> caller join still owed; 137 open. 376 of the 396 CLOSED rows these definitions serve
> depend on at least one definition that is not yet TOTAL. No reachable input on which the
> wrapping binary accepts and the checked model rejects is known. Removal condition: all 225
> definitions in (a), (b) or (c) on the final closure, or the owner records R22 as a retained
> trust row, named in the claim's first sentence.

The 2021 figures (35 TOTAL / 63 ACCEPTED-ONLY / 48 OTHER of 146 statements) concern a
different object (theorem statements at 6546eb41 and b2727acd) and are superseded for this row.

## 6. Receipts and resources

- NPH_COMPILE.tsv: target, exit, wall, peak RSS, cgroup peak, swap, caps, source sha256,
  revision and axiom summary for each scope.
- NPH_ATTEMPTS.jsonl: admission, submission and result events.
- NPH_L00N/: receipts, sources and xz logs.

9 of the 30 budgeted Lean scopes were used, serially, each at MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax 0, TasksMax 64 (lean -j1 -M7000, 180 s timeout). Every launch was admitted with
host scope count < 6, disk ≥ 40 GB and the 55 GiB reservation barrier.

| Scope | Target | Result |
|---|---|---|
| L001 | API probe | diagnostic, never credited |
| L002–L004 | NPH_R22FieldRef | failed; each followed by a source change |
| L005 | NPH_R22FieldRef | accepted, 17 axiom lines |
| L006 | NPH_R22FieldCopies | accepted, 111 |
| L007 | NPH_R22CM31 | failed |
| L008 | NPH_R22CM31 | accepted, 26 |
| L009 | NPH_R22Weak | accepted, 13 |

Peak process RSS was 5,473,920 KiB (L008), wall time at most 3.6 s, and swaps were 0
throughout. All 167 accepted `#print axioms` lines are within [propext, Classical.choice,
Quot.sound]. No Kani run, extraction, full manifest replay, push or host deletion was made.

Host-side read-only helpers: NPH_census_host.py (gate body census) and NPH_existing_host.py
(textual screen of closure theorems naming each definition; labels are not judgments). Their
outputs are NPH_CENSUS_BODIES.json.xz and NPH_EXISTING_SCREEN.json.xz.

These modules are additive evidence. They are not in the TAS_FinalB import closure, so a
release replay must include them for the CheckedVsWrapping row to cite them.

Next concrete deliverable: the limb ≤ P caller invariant for the 28 domain-lemma kernels, plus
Q.raw. That moves about 230 rows from domain-only toward (b). After it come the mechanical
index/cursor loop bodies.

Target not yet established.
