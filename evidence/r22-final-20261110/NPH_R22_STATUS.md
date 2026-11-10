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

Counts in this section are as first published (L001–L009). Section 7 supersedes them.

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

## 7. Continuation (lead instruction 2026-11-10, after merge of ac90858a331)

Four more scopes were used (L010–L013, 13 of 30 in total; L010–L012 failed on proof-script
details, each followed by a change). The new module is NPH_R22QRawShift, accepted in L013:
2.43 s, 5,449,788 KiB, swap 0, 5 axiom lines, all [propext, Classical.choice, Quot.sound].

**Updated counts (225 checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL | 60 |
| DIRECT (c) | 1 |
| domain lemma proved, caller join open | 31 |
| precondition proved from the callers (b) | 0 |
| open | 133 |

Rows are unchanged: 376 of 396 still depend on a definition that is neither TOTAL nor DIRECT.

**Item (2), Q.raw.** `qraw_eq` proves FIo_QRaw.canonical.Q.raw definitionally equal to the
AspisR1CanonicalQRawUnified body; both closure types are `Unit`, so the 2026-11-10 concern
about distinct closure types was unfounded. `fio_qraw_total_of_canonical_limbs` transfers the
closure theorem AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs to the second copy.
The caller join (every Q reaching Q.raw has limbs ≤ 2^31-2) is not proved. It is the same
obstruction as item (1) below.

**Item (3).**
- fibre_point is DIRECT. Its only overflow-checked operation is `index >>> 9#i32`, which
  succeeds for every index (`fibre_shift_ok`). Its other steps are array indexing, a pure `&&&`
  and two callbacks. None of them is overflow-checked in the body, so the checked and wrapping
  executions of the body coincide. The callbacks' own arithmetic is the R22 item of the
  installed CM31 kernels.
- transport row_loop.body: `row_shr_ok` and `row_shl_ok` make both checked shifts safe when
  the loop index is below 16 and the TAU entry read is below 16. The reached-domain fact
  (iter.end ≤ 16, PCQH-C5 and NPE_) and the TAU constant-table bound are not composed here,
  so it stays domain-only.

**Item (1), the limb ≤ P caller invariant: not established; an obstruction is reported.**
NPH_callers_host.py (output NPH_CALLERS.json.xz) lists every reached definition that names one
of the 28 kernels. There are 76 distinct callers. 48 are inside the field modules: CM31/QM31
add, sub, mul, square, double, mul_by_r, inv_with and similar. The kernel closure of
NPH_R22Weak extends to these, but that extension still needs each body written out. 28 callers
are outside the field modules. Among them are hand-written ops installers and model glue:
NBF_BasisInstall.install, AspisR1.SAQ_Geometry.install, AspisR1.SAQ_Query.install,
LIBC_QueryOps.seed, NJJ_QueryOps.concrete, NFN_NEW_GeometryContextGeneric.replace,
R17CurrentCM31Semantics.operations, R17CurrentM31Semantics.operations,
RawExtractedSemanticCallOpsV20.resultMap, NNU_QueryFieldBase.toQM and others (listed in the
JSON). They place the kernels into callback records. The gate code then calls those
callbacks on values it computes itself.

The ledger's field-domain roots, for example NHV_NEB_FieldDomains.cm_arguments and
cm_add_calls, take canonicality (canonC/canonQ/canonE) as a hypothesis. They do not prove it.
So no per-kernel lemma "the arguments at the reached call sites are ≤ P" follows from the
closed rows as they stand. Proving it means following values through every callback record
to their gate producers. This is the 2021 backend obstruction (R22OverflowWorkerBackendObstruction),
now located at named ops installers.

Recommended route (one job): give the M31 carrier of the installed ops records a ≤ P
subtype, or add an invariant field to each Ops record. Then prove once that every producer
respects it:
- the strict decoders return none for ≥ P (AspisR1.ActualDecodeKStrictQM31Parser.success_has_strict_limbs
  is in the cone);
- the samplers are canonical;
- the constants are canonical;
- the `& P` mask gives ≤ P;
- the kernels preserve it (NPH_R22Weak).

This changes the statement of the ops interface. A lead or owner decision is needed before any
module is re-pinned. No caps were raised, and nothing was re-run unchanged.

**Item (4) is not started.** A body scan (of NPH_CENSUS_BODIES.json.xz) shows 32 open bodies whose only checked arithmetic is one increment
`x + 1#usize`. In each case x is either guarded by `x < n` or an iterator index below the range
end; this was checked per body by reading, not proved. Examples: digest_is_canonical ×2 (51 and 32 rows), the NCV/NCX loops, the Poseidon
lane loops, array_from_fn_copy_loop and finish_owned_loop.body. These are arithmetic-safe for
every input, by the same argument as fibre_point, once a generic `x < n → x + 1 ok` lemma and
a per-body lemma are written. This is the next mechanical deliverable. The other 17 scopes
were not used.

**Eight definitions served by closed rows, not by the headline** (absent from both the
deployed_splitB and deployed_charge raw cones):
- AspisR1BatchedWeightsExtraction BatchedWeights.push, and push_loop.body
- S8Kani2MutableExtraction BatchedWeights.push, and push_loop.body
- AspisR1FinishRelationCurrent.verifier.finish_relation_round
- NCV_Reference valid_sequences_loop.body
- NCV_Reference zero_sequences_loop.body
- NDH_TranscriptReference.absorb_ref

No reachable input on which wrapping accepts and checked rejects was found.

Target not yet established.

## 8. Item (4), first batch (lead decision 2026-11-10: no ops-interface change; limb bound as a separate invariant)

Two more scopes were used: L014 failed on an unqualified type name, and L015 accepted
NPH_R22Loops (2.40 s, 5,451,088 KiB, swap 0, standard axioms). That makes 15 of the 60 used.
- `usize_succ_ok` (generic): `x + 1#usize` succeeds whenever x < n for a machine usize n.
- `pair_forest_accounts_digest_is_canonical_body_total` and
  `pair_tree_profile_digest_is_canonical_body_total`: both AspisR1TerminalDecoder
  digest_is_canonical loop bodies are checked-total for every input.

**Counts now:** 62 TOTAL, 1 DIRECT, 31 domain-only, 0 (b), 131 open. Rows: 370 of 396 still
depend on a definition that is neither TOTAL nor DIRECT; 26 are served only by TOTAL or DIRECT
definitions.

**Remaining.** 30 of the 32 single-increment bodies are not yet done, largest fan-out first:
- the Poseidon lane loops (28–34 rows);
- array_from_fn_copy_loop (31);
- finish_owned_loop.body (21);
- the NCV/NCX reference loops (9–20).

Each needs its own guard read and one per-body lemma in the same pattern. After that come
items (i)–(iii) of the separate limb invariant, which keeps the ops records and closed-row
statements unchanged.

Target not yet established.

## 9. Item (4) complete (continuation worker, 2026-11-10)

Two scopes were used, L016 and L017, both accepted on the first attempt (17 of the job's
scopes in total; this worker's budget is 45, 2 used). NPH_R22Loops2 took 2.75 s and
5,425,672 KiB; NPH_R22Loops3 took 2.57 s and 5,647,324 KiB. Swap was 0 in both. All 31
`#print axioms` lines are within [propext, Classical.choice, Quot.sound].

All 30 remaining single-increment bodies are judged. Each one reuses the generic
`NPH_R22Loops.usize_succ_ok` and has one lemma of its own.

- **TOTAL (a), 5 bodies.** The bodies are NCX zero_loop, NCV zero_loop, NCV eq_digest_loop,
  and NCV valid_sequences_loop and zero_sequences_loop. The last two are outside both top
  cones. Each body is checked-ok on every input. Its indexing is in bounds under its own
  guard, and its only arithmetic is the guarded `i + 1`.
- **DIRECT (c), 25 bodies.** These are the Poseidon lane loops, array_from_fn_copy_loop,
  finish_owned_loop.body, finish_query_dot_loop.body, the two samplers, semantic_boundary,
  values_owned_reference, sort_rows, the NCX and NCV equal_loop bodies (an index into `v` can
  fail when `v` is shorter, so they are not TOTAL), and the three claim range-iterator bodies.
  Two pieces of evidence support each one:
  1. A mechanical screen (NPH_loops_update.py, output NPH_LOOPS_SCREEN.json). It finds that
     the body's only overflow-checked binding is one `x + 1#usize`. The screen is textual.
  2. A Lean lemma `<name>_step`. It proves that increment safe under the guard as the body
     writes it.

  For the range-iterator bodies, the guard is the `some point` result of IteratorRange.next.
  `NHI_RangeProgress.some_next`, which is in the replayed closure, gives `point < iter.end`.
  semantic_initial_and_absorption has a different increment, `poseidon2.RATE + 1`. It is the
  constant 9 (`semantic_initial_rate_succ_ok`).

  The reasoning matches fibre_point. Indexing, update, comparisons and `&&` are not overflow
  checks: bounds checks stay on in both profiles, so the two semantics agree on them.
  Callees are separate cone definitions with their own R22 judgment. So when the callees
  agree, the checked and wrapping executions of the body coincide.

**Counts now (225 checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 (64 checked, 3 mixed) |
| DIRECT (c) | 26 |
| domain lemma proved, caller join open | 31 (28 checked, 3 mixed) |
| precondition proved from the callers (b) | 0 |
| open | 101 (99 checked, 2 mixed) |

The checked and mixed definitions touch 396 CLOSED rows. 365 of them still depend on at least
one open or domain-only definition, and 31 are served only by TOTAL or DIRECT definitions. The
row gain is small because the field kernels (31 domain-only definitions, up to 186 rows
each) and the accumulator families lie under almost every row.

The `counts_by_class` block in NPH_R22_CONE.json had been left at the L009 values. It is now
recomputed from the per-definition judgments.

The eight definitions outside both top cones are unchanged in membership. Their judgments now
stand as follows.
- NCV_Reference valid_sequences_loop.body and zero_sequences_loop.body: TOTAL (this batch).
- AspisR1BatchedWeightsExtraction BatchedWeights.push and push_loop.body: open.
- S8Kani2MutableExtraction BatchedWeights.push and push_loop.body: open.
- AspisR1FinishRelationCurrent.verifier.finish_relation_round: open.
- NDH_TranscriptReference.absorb_ref: open.

Next: items (i)–(iii) of the separate limb ≤ P invariant (lead decision of section 8).

Target not yet established.

## 10. Limb ≤ P invariant, items (i)–(iii), and row_loop (continuation worker, 2026-11-10)

Five more scopes were used: L018–L022, 7 of this worker's 45. L020 and L021 failed on the
reduction of a let-pair in the proof script. The script was changed after each failure.
Every accepted module is within [propext, Classical.choice, Quot.sound]. Peak RSS was
6,022,644 KiB (L018) and swap was 0. The lead decision holds: no ops interface and no merged
module is changed. Each statement is a separate lemma about the existing definitions.

**(ii) Installer lemmas, NPH_R22Installers (L018).** The weak domain is `W x := x.val ≤ P`.
For the M31-level callbacks, each record's constants are W and each of its callbacks maps W
inputs to an ok W output.
- `QueryM31W` (op4–op8: constants 0 and 1, QA M31.sub, QA M31.mul, and add x x or
  S7 double) for:
  - NBF_BasisInstall.install (any ops)
  - SAQ_Query.install (any ops)
  - LIBC_QueryOps.seed
  - NJJ_QueryOps.concrete
- `GeometryM31W` (op7–op10) for SAQ_Geometry.install.
- R17CurrentM31Semantics.operations: mul, double and sub.
- R17CurrentCM31Semantics.operations: new and mul, the latter through QA_CM31_mul_weak.
- S7Kani3BasisOuter.double and t2.

Not covered:
- query op1–op3 and op9–op21 (wide/extension callbacks: SAQ_Arithmetic.add/mulK,
  SAQ_MixedSource.mulE, opening, line/circle queries, dots, decoder read, push);
- geometry op14/op15 (SAQ_Geometry.line and point, through line_node and fibre_point);
- NFN_NEW_GeometryContextGeneric.replace;
- the RawExtractedSemanticCallOpsV20.resultMap glue;
- the toQM conversions (NNU_QueryFieldBase, CurrentWideBaseBridge).

**(i) Producer lemmas, NPH_R22Producers (L019).**
- `decodeK_strict_limbs_lt` and `s8_strict_limbs_lt`: every QM31 that the DecodeKFullV10 or
  S8OwnedP6 strict decoder returns has all four limbs < P. These follow from the closure
  theorems success_has_strict_limbs.
- For the CW and QA copies, M31.double, CM31.add/sub, mul_by_r and QM31.add/mul (plus CW
  QM31.sub) map limbs ≤ P to ok limbs ≤ P. This extends NPH_R22Weak from the 28 kernels to
  their field-module callers.
- The `& P` mask producer is the existing `NPH_R22FieldRef.and_P_le`.

Not done: producer lemmas for the samplers and the constants (beyond the 33 already TOTAL),
and the same tower lemmas for the SM, SC, FIq and R72 copies. The pattern is identical: one
templated block per copy.

**(iii) Reached-execution invariant: not composed.** No kernel's precondition is yet proved at
its reached call sites, so no definition moves from domain-only to (b). The hypotheses
canonC/canonQ/canonE of NHV_NEB_FieldDomains are not yet discharged. Two findings bear on
the walk.
- The census lists 0 callers for AspisR65Field M31.add/neg and AspisR66Field M31.add/sub/neg
  (22–25 rows each), yet they are in the cone. They must be reached through a path the
  literal-name census does not see, for example a trait instance or a callback record. That
  path has to be located before their join can be stated.
- The wide/extension callbacks above sit between the decoders and the kernels on the
  094/345 path. The join for SelectedMaskProbe/CurrentWide/QA M31.add/sub and CM31.mul
  (110–186 rows each) needs the W statement for those callbacks first.

**row_loop.body is DIRECT (NPH_R22RowLoop, L022).** transport.TAU is the constant
[3,4,2,0,1]. Both semantics bounds-check the read TAU[d], so any iteration the wrapping
program completes has d < 5. Under that condition `row_loop_body_ok` proves the checked body
ok. For d ≥ 5 both semantics reject. So the reached-domain fact (iter.end ≤ 16) is not
needed, and the judgment is DIRECT for every input.

**Counts now (225 checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 (64 checked, 3 mixed) |
| DIRECT (c) | 27 (26 checked, 1 mixed) |
| domain lemma proved, caller join open | 30 (28 checked, 2 mixed) |
| precondition proved from the callers (b) | 0 |
| open | 101 (99 checked, 2 mixed) |

Rows: 365 of 396 still depend on at least one open or domain-only definition, and 31 are
served only by TOTAL or DIRECT definitions. row_loop's 24 rows all also depend on other
non-closed definitions, so the row count does not move.

The eight definitions outside both top cones: NCV valid_sequences_loop.body and
zero_sequences_loop.body are TOTAL. The BatchedWeights push/push_loop.body pairs (×2),
finish_relation_round and NDH absorb_ref remain open.

No reachable input on which the wrapping binary accepts and the checked model rejects was
found.

Next concrete deliverables, in order:
1. W lemmas for the wide/extension query callbacks (SAQ_Arithmetic.add/mulK, mulE) and the
   tower lemmas for the SM/SC/FIq/R72 copies.
2. Locate how the R65/R66 kernels are reached.
3. The bind-stepping join along the 094 body (NOC_ConvLeaves/Semantic/094) for the
   SelectedMaskProbe kernels, discharging canonC/canonQ/canonE of NHV_NEB_FieldDomains from
   the decoder and installer lemmas.

Target not yet established.

## 11. R65/R66 reach path and step-2 W-lemmas (continuation worker, 2026-11-10)

Three scopes were used, L023–L025, all accepted on the first attempt (3 of this worker's 38).
Peak RSS was 6,863,864 KiB (L025) and swap was 0. All 83 `#print axioms` lines are within
[propext, Classical.choice, Quot.sound]. The lead decision holds: no ops interface and no
merged module is changed.

**Step 1: how the R65/R66 kernels are reached.** A textual screen over the L187 closure
sources (NPH_r6x_scan.py, output NPH_R6X_REFERRERS.json) lists every declaration whose body
names AspisR65Field/AspisR66Field `field.M31.add/sub/neg`. There are 23 referrers. The 13
reached ones are all theorems: the definitional transport lemmas
AspisV8R19.SamplerClosureCircleScalarTransport.add_eq/sub_eq/neg_eq
(`AspisR72Sampler.field.M31.op = AspisR66Field.field.M31.op`, by simp on the two bodies),
AspisV8R19.QuarticBaseExecution.add_eq/neg_eq (R66 = R65) and the R19
add_encode/add_success/neg_encode/sub_encode lemmas. The 10 definition referrers
(R65/R66 CM31.inv_with, CM31.sub/neg/mul, M31.double, mul_by_r) are not in the REACHABLE
list. So no reached definition body executes an R65 or R66 kernel. They are in the cone as
proof-level references for the AspisR72Sampler kernels, which are pointwise equal to them.
Their execution sites are therefore the R72 sites, and their caller join is the R72 join.
The path is recorded as `reach_path` on the five definitions in NPH_R22_CONE.json. Their
judgment stays domain-only. Deciding whether a proof-only reference needs any R22
judgment at all is left to the lead. The screen is textual, not a Lean-level constant walk.

**Step 2: W-lemmas (W x := x.val ≤ P).**
- NPH_R22Callbacks (L023, 23 statements).
  - The CW tower above QM31 (WideExact add/sub/mul, mul_u, and M31/CM31/QM31/WideExact
    mul_m31) maps W inputs to an ok W output. mul_m31 does this for any M31 operand, since
    the operand goes through `% P` or M31.mul, which is total.
  - The query callbacks: op2 SAQ_Arithmetic.add and op9 mulK; op3 SAQ_MixedSource.mulE
    (W wide operand, any power, since canonicalQ reduces it); op1 fromK and op10 fromM;
    op16 SAQ_LineQuery.line and op17 FIp_CircleQuery.circle (W alpha and values, any
    inverse array, ok W). op21 SAQ_Decoder.read is a producer: every successful output has
    all eight limbs < P (ExtractedRecordByteCanonicality.slice_success).
- NPH_R22Towers (L024, 48 statements). These are the SM, SC, FIq and R72 tower lemmas in the
  NPH_R22Producers pattern: M31 mul/double/neg; CM31 add/sub/neg/double/new/mul_m31/square
  (the weak Karatsuba bound (2P)^2 < 2^64; for R72 through r23_product_u32_bounded);
  mul_by_r; and QM31 add/sub/mul/mul_m31/square. Not covered: R72 QM31.mul, whose first
  step r24_canonical_mul is OPEN (NO_FROZEN_COUNTERPART), and the FIq prepared-multiplier
  family.
- NPH_R22Callbacks2 (L025, 12 statements).
  - fibre_point under the installed R17 CM31 operations: for every fibre index, either the
    checked body is ok with both coordinates W, or the TABLE_B index `index >>> 9` is
    ≥ 512. That is an out-of-bounds read, bounds-checked in both profiles. The table entries
    are < P by NEA_TableCanonical.readA/readB, which is in the cone.
  - The same disjunction gives geometry op15 SAQ_Geometry.point and op14 SAQ_Geometry.line
    (line_node with the R17 M31 operations).
  - NFN_NEW_GeometryContextGeneric.replace preserves the GeometryM31W record whenever the
    installed sub/double preserve W.
  - The conversion glue (NNU_QueryFieldBase.toQM, CurrentWideBaseBridge toQM, the
    RawExtractedSemanticCallOpsV20 resultMap and its genQ/probeC copies) copies limbs
    unchanged, so W transfers.

Not covered by step 2:
- op14 push (S7Kani2OwnedPush.push_owned);
- op20 dots, whose output canonicality is proved in FIp_DotsOutputCanonical.all, but that
  module is outside the L187 closure and is not imported;
- op11 opening, op12/op13 index and op18 forQuery (no field arithmetic, or values that feed
  only the M31.mul of line/circle, which is total);
- producer lemmas for the samplers (their digit and div loops are OPEN).

**Counts: unchanged.** Step 2 proves interface lemmas only. No kernel's precondition is yet
established at its reached call sites, so no definition moves.

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 30 |
| precondition proved from the callers (b) | 0 |
| open | 101 |

Rows: 365 of 396 still depend on at least one open or domain-only definition.

Target not yet established.

## 12. Step 3: call-site joins on the tx1 (094) query path (continuation worker, 2026-11-10)

Three more scopes were used, L026–L028, for 6 of this worker's 38. L026 failed because
alpha_sites lost the read value after `cases` on an ok-equality. The script was changed to
`subst`. L027 and L028 were accepted. Peak RSS was 6,868,148 KiB and swap was 0. All 16
accepted `#print axioms` lines are within [propext, Classical.choice, Quot.sound].

**Which dictionary 094 actually runs.** The tx1 query loop executes
Port3_NativeQueryBody.verifier.candidate.query_values on two dictionaries:
- Dcon = NFS_QueryOps.installed NJJ_QueryOps.concrete;
- Dsel = NFS_QueryOps.installed (select LIBC_QueryOps.seed).

The two agree on reached steps (NOC_QueryLink.values_eq). `installed` replaces op2/op3/op9
with NBO_FieldSemantics.add/product/power (the SelectedMaskProbe QM31 tower) and op4–op8
with NBF_BasisInstall (QA M31 sub, mul and add x x). So the SAQ_Arithmetic/MixedSource
callbacks of section 11 are not the ones 094 runs at op2/op3/op9. The CurrentWide tower
enters 094 through op16 line and op17 circle.

The input packet NFS_PacketRoot.Domain carries canonicality for alpha[0] and alpha[1], the
inverses, line_z, the dots inputs g, and the accumulator rhs, power and rho. At 094 it is
produced by NOC_QueryDomain.domain on the 57607-byte proof.

**NPH_R22Join094 (L027) and NPH_R22Join094Step (L028).** Sites discharged; each kernel call
there is ok with canonical or W output:
- Node sites, for every input: in query_values, `op7 z z; op8; op5; op6 · one`; in
  accumulate_batched_with_node_loop0.body, the same with m = op5 = 1. These are the QA
  M31.mul, M31.add (doubling) and M31.sub calls. They hold for every input because the
  arguments are fresh mul outputs (< P) and the constant 1.
- Line and circle sites: op16 on alpha[1] and op17 on alpha[0]. Both alphas come from the
  Domain (alpha_sites). Every CurrentWide kernel call inside line/circle receives W
  arguments, and the outputs are canonical.
- Accumulate tail sites: op3/op2/op9 = NBO product/add/power on the Domain rhs/power/rho and
  on a WideCanonical value. This covers every SelectedMaskProbe QM31/CM31/M31 call inside
  them, through the existing NBO_FieldSemantics *_total lemmas.
- `query_step_sites` composes the step. The op21 opening values are canonical
  (NFS_CallerDomains.fields) and the op20 dots are canonical (NFS_CallerDomains.dots). From
  them, the circle and line calls are ok. The line output is WideCanonical
  (NFS_AccumDomain.line), so the three tail calls are ok. All of this rests on the packet
  Domain alone.

**Every other reached site: not composed.** NPH_sites_scan.py (output NPH_SITES.json) is a
textual screen. It lists every reached definition outside a family's own namespace whose body
calls a function of that family:

| Family | Executing sites | Covered here | Uncovered (examples) |
|---|---:|---:|---|
| CW | 6 | 3 | FIn_Polynomial.mul, FIn_Primitives.add, SAG_StageScale.mulM |
| QA | 40 | 9 | the SAF_/SAP_ Outcome families, Port4C_InverseExecution, SAQ_Inverse.source, NFN geometry prefix/polynomial, S7Kani2PrefixLoop, AspisR1CurrentWideMul tower |
| SM | 10 | 3 | FIp_SemanticArithmetic add/mul, NJB_PackLaw.reference, ExtractedMaskQmPackBase4 |
| FIq | 53 | 0 | the NJL_/NJX_/NKI_ Merkle and absorption references, FJe_Sum3 bridges, FIv_FoldsTotal.body |
| SC | 0 | 0 | none outside its namespace (the callers are inside AspisR1SemanticCallExtraction.r1_semantic) |
| R72 | 0 | 0 | none outside its namespace (the callers are the sampler bodies) |

Callers inside a family's own namespace are not in this list and are also open, for example
SM state_only_hiding, FIq pool_v1/state_only_poseidon and the R72 sampler. So no kernel has
its precondition established at every reached site, and no definition moves to (b).
NPH_R22_CONE.json records, per domain-only kernel, the sites discharged and the uncovered
sites (`caller_join_progress`).

**The NHV_NEB_FieldDomains canonC/canonQ/canonE discharge was not done, and it would not
change the R22 counts.**
- NEB_FieldDomains (module NHV_NEB_FieldDomains) is not in any L187 replay REACHABLE list:
  not deployed_splitB, deployed_charge, NNH8_DeployedOuter or fail_sub_rec. It is the root
  of the separately replayed rows TX1:001/TX2:001 (NKT_ROOT_REACHABILITY.json).
- Its kernels are the FIo_Native M31/CM31 copies. FIo_Native.aspis_core.field.reduce_u64 is
  WRAPPING in the cone, and the FIo_Native add/sub/mul are not among the 225 checked or mixed
  definitions (PCXD_R22_SPLIT).
- So discharging canonC at FIo_Native call sites would discharge a premise of those
  functional rows. It does not move any R22 judgment.

No such instance theorem was stated. The 094 joins above discharge the analogous canonicality
for the checked tower copies that 094 actually executes.

**Counts (225 checked or mixed definitions): unchanged.**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 30 |
| precondition proved from the callers (b) | 0 |
| open | 101 |

Rows: 365 of 396 still depend on at least one open or domain-only definition, and 31 are
served only by TOTAL or DIRECT definitions.

No reachable input on which the wrapping binary accepts and the checked model rejects was
found. No site was found where the limb bound cannot come from a producer: every 094
query-path value traced here starts at a strict decoder, a canonical table, the Domain, or a
fresh M31.mul output.

**Not reached in this run (scope budget unused: 32 of 38).** These are the 345 body, the
tx2 common body (NOF_CommonConverse), and the uncovered sites above. The next deliverables,
in order:
1. Site joins for the remaining CW sites (FIn_Polynomial.mul, FIn_Primitives.add,
   SAG_StageScale.mulM) and the remaining SM sites. With these, CW and SM are the closest to
   (b).
2. The QA SAF_/SAP_ Outcome families and the inverse executions.
3. The in-namespace callers (state_only_hiding, pool_v1, the samplers).
4. The FIq Merkle/absorption family, which has the largest site count.

Target not yet established.

## 13. Tightened site checklist and the CW, SM and QA site lemmas (continuation worker, 2026-11-10 evening)

Four scopes were used, L029–L032 (4 of this run's 32). L030 failed because `simp only` left
witness metavariables for two closure results. The script was changed to give explicit
witnesses, and L031 accepted the same module. Peak RSS was 6,021,140 KiB (L032) and swap was
0. All 43 accepted `#print axioms` lines are within [propext, Classical.choice, Quot.sound],
and there is no sorry. The lead decision holds: no ops interface, merged module or closed-row
statement is changed.

**Ruling 1 (proof-only references).** The five R65/R66 kernels (AspisR65Field M31.add/neg and
AspisR66Field M31.add/neg/sub) are now NOT_EXECUTED in NPH_R22_CONE.json. Each keeps its
`reach_path`, and the previous judgment is kept in `nph_judgment_before_20261110_evening`.
They are excluded from the obligation, so **the denominator is now 220** (225 minus 5). Their
execution sites are the AspisR72Sampler sites of the pointwise-equal kernels, and those keep
their own judgment.

**Step A, tightened screen (ruling 2).** NPH_sites_scan2.py replaces NPH_sites_scan.py, and
NPH_sites_status.py annotates its output. The result is NPH_SITES.json. The screen changes in
four ways:
1. It reads the replayed L187 src tree (host codex-cx-replay-l187-20261109/src, from its
   l187_src.tar.xz). The old screen took the first committed blob listed in
   L187_CLOSURE.json. For 122 modules that list holds several distinct sources, and for
   AspisR1SelectedMaskProbe.Funs the first blob is a 10 KB early probe with no CM31.mul.
   The replayed file has sha256 4aa955ab…, which matches none of the listed blobs.
2. It resolves names through the declaring namespace chain and every `open`. FIq_Native alone
   is opened in 637 modules, so the old literal-prefix match missed most calls.
3. It includes callers inside each family's own namespace, among them the hand-written
   wrappers AspisR1CurrentWide.Proof.finishAdd/finishArithmetic/… and the extracted
   state_only_hiding and sampler bodies. It also follows one alias level, such as the
   AspisR1CurrentWideMul abbrevs of the QA tower.
4. A site is counted only when its body reaches a **domain-only** kernel of the family. Sites
   that call only TOTAL kernels (M31.mul, mul_m31, reduce_u64) or CM31.new carry no
   precondition. They are listed under `_dropped_from_old_screen`: the 25 QA SAF_/SAP_ Outcome,
   inverse, prefix and basis-level sites (M31.mul only), CW SAG_StageScale.mulM (mul_m31 only),
   the 5 SM qm31_pack_base4 sites, and 18 FIq sites.

The screen is textual. It cannot see calls made through notation, instance resolution or
callback records, so it is the checklist, not a proof of completeness.

| Family | Sites (new) | Old executing | Status after this run |
|---|---:|---:|---|
| CW | 26 | 6 | 21 W_LEMMA, 5 OPEN |
| QA | 24 | 40 | 23 W_LEMMA, 1 EVERY_INPUT |
| SM | 40 | 10 | 29 W_LEMMA, 2 EVERY_INPUT, 3 JOINED_094, 1 NOT_EXECUTING, 5 OPEN |
| SC | 18 | 0 | 18 OPEN (not examined) |
| R72 | 17 | 0 | 17 OPEN (not examined) |
| FIq | 238 | 53 | 238 OPEN (not examined) |

W_LEMMA means a Lean lemma shows that W inputs at the site give ok W outputs, so every kernel
call inside receives W arguments. It is conditional on the site's own inputs, which come from
the callers listed per site in `contexts_direct_callers`. EVERY_INPUT means the site is ok
with W output for every input, so it is a frontier.

**Step B, CurrentWide: NPH_R22JoinCW (L029, 11 statements).**
- `FIn_field_W` (producer). Every successful FIn_Primitives.field read is W. It goes through
  finishField_success_canonical.
- `FIn_add_W`, `FIn_mul_W`, `finishAdd_W`, `claimAdd_W` and `claimMul_W` are the W-lemmas for
  the FIn wrappers, the hand-written finishAdd and the CurrentClaimSumModel WideExact
  add/mul copies.
- `poly_step` and `poly_W` cover the extracted Horner FIn_reference.polynomial on
  FIn_ExtractInstall.arithmetic. For a W point, every step is ok and W, and the whole
  polynomial is ok and W when all seven reads succeed.
- `round_sites` covers Stage2 finishRelationRoundWithOps on any FinishOps whose
  field/add/mulM/polynomial slots are the deployed ones (those of IDa_Deployed.finish). The
  lhs add is ok and W on successful reads, mulM is ok for every claim, and the polynomial is
  ok and W for a W alpha.

**CW is not complete. Its kernels stay domain-only.** These contexts are open:
- the W bound of the finish Prepared p.alpha[0] and p.alpha[1], which round_sites assumes;
- the finish dot SAG_DotAdapter.kernel (finish_query_dot under finishConcreteField);
- FIn_Install.finishOps;
- the three CurrentPreparedClaim sum loops;
- every query dictionary other than the 094 Dcon/Dsel that installs line, circle or the
  SAQ_Arithmetic/MixedSource callbacks: NJJ_Common.query, NNH_Tx2SourceConfiguration.fill,
  NNH_HostSeed.m0, NNH_Run5bQuerySlots.model, NNX_QueryOutput.run, LIBC_QueryLoop.model,
  NFS_QueryOps.base, SAQ_LineQuery.install, FIp_Install.select and SAQ_QuerySource.install.

**Step C, SelectedMaskProbe: NPH_R22JoinSM (L031, 27 statements).**
- `PM_new_ok`, `PM_mul_W` and their closures cover PreparedQm31Multiplier. mul is ok and W for
  any prepared value and a W right operand, because the stored components enter only
  M31.mul.
- RPv QM31.sub.
- state_only_hiding:
  - cm31_mul_i/cm31_mul_r and mul_tower_basis, for coordinate < 4; `column &&& 3` < 4 is
    proved;
  - mask_power_26;
  - one iteration of each kernel-calling loop body (`linears_body_site`, `coeff_site`,
    `loop2_body_site`, stated over arrays whose every successful read is W);
  - the straight-line tails `linears_tail` and `mask_tail_sites`.
- FIp_SemanticArithmetic add/mul.
- PoseidonPreparedProductCells.rightBuilder.
- The qm31_sum_products3_prepared_loop0 step.
- `karatsuba_W` and `karatsuba_closure_W`: qm31_from_karatsuba_channel_sums is ok with W output
  for **every** input, because the limbs pass reduce_u64 first.

**SM is not complete. Its kernels stay domain-only.** These are open:
- the four loop wrappers (the loop compositions of the body lemmas);
- the W invariant of the 27-entry coefficient array across the loop0/loop1 updates;
- FIp_SemanticArithmetic.mask, whose inputs c1, mask_only_c1, g and point come from the
  semantic-boundary installers IDa_Deployed.boundaries/NNG_*;
- the right operands of qm31_sum_products3_prepared.

**Step D, Qm31ArithmeticProbe: NPH_R22JoinQA (L032, 5 statements).**
- The CurrentWideMulCanonical copies QM31.sub, mul_u and WideExact.mul are W-preserving.
- NFN_NEB_GeometryPrimitives.install satisfies GeometryM31W on op7–op10.
- NFN_NEW_GeometryPolynomial.cohort is ok and W for every input.

The Outcome and inverse sites that the lead named for step D call only QA M31.mul, which is
TOTAL. They impose no precondition and leave the checklist. Every QA site now has a lemma.
**QA is still not complete**, because the installer W-lemmas are conditional on what the gate
passes outside the 094 joins. These remain open:
- the installer contexts outside 094;
- NFN op14/op15 under NFN_NEA_FieldProduct.ops;
- the callers of CurrentWideMul WideExact.mul.

**Step E was not started**: the 345 body walk and FIq. The FIq checklist grew from 53 to 238
sites once `open` resolution was added.

**Counts (220 executed checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 25 |
| precondition proved from the callers (b) | 0 |
| open | 101 |
| NOT_EXECUTED (excluded) | 5 |

Rows: the executed checked or mixed definitions touch 396 CLOSED rows. 365 of them still
depend on at least one open or domain-only definition, and 31 are served only by TOTAL or
DIRECT definitions. The figure does not move, because the five excluded kernels' rows are all
also served by other open definitions.

No executing site was found that passes a value without a producer for its limb bound. No
reachable input on which the wrapping binary accepts and the checked model rejects was found.

Next, in order:
1. The finish Prepared alpha link, then the finish dot and the CurrentPreparedClaim sum loops.
   With the non-094 query dictionaries, these close CW.
2. The semantic-boundary operands and the coefficient-array invariant, which close SM.
3. The QA installer contexts outside 094.
4. SC/R72 (35 sites, mostly extracted towers and two sampler entry points).
5. FIq (238).

Target not yet established.

## 14. CurrentWide contexts composed from producers on the tx2 body (continuation worker, 2026-11-10 night)

Four scopes were used, L033–L036 (4 of this run's 40). L033 failed on an unqualified name
(Stage2Finish.verifier.finishRelationWithOps) and on the fixed W of FIn_WeightsInstall; L035
failed on one list-index goal in claim_initial. Each script was changed before the next scope.
L034 accepted NPH_R22JoinCW2 (3.54 s, 6,881,052 KiB) and L036 accepted NPH_R22JoinCW3
(3.57 s, 6,867,308 KiB). Swap was 0. All 28 accepted `#print axioms` lines are within
[propext, Classical.choice, Quot.sound]; there is no sorry. The lead decision holds: no ops
interface, merged module or closed-row statement is changed.

**Producer for the finish Prepared.** VTop_Stages tx1 never calls op19; the finish runs only in
tx2_common, on the pair (p, a) returned by the tx2 resume (op18, NJJ_Common.resume).
`NPH_R22JoinCW2.entered_domain` derives NID_ResumeFields.Domain p a from the resume success
alone, with the checkpoint width from the same success (NKE_ResumeWidth.checkpoint). The
Domain comes from the strict checkpoint decoders: NJC_EReaderResults.naturalE returns Ok only
under CanonicalWide. No later call's success is used, so the fact is available at every
later site in execution order.

**CW contexts closed by NPH_R22JoinCW2 (L034, 19 statements).**
- Finish alpha: `resume_alpha_W` (both alpha reads are W). `tx2_finish_round`: on the tx2
  native finish (NIG_Slots.installed r = finishRelationWithOps on Port3_FinishStage.release
  (IDa_Deployed.finish r), `tx2_finish_body`), the lhs add is ok and W on successful reads,
  mulM is ok for every claim, and every Horner step on the read alpha is ok and W.
  `tx2_finish_round_entered` takes the Domain from the resume success itself.
- Finish dot: `kernel_slots` proves by rfl that SAG_DotAdapter.kernel equals finish_query_dot
  on the same record with add, mulM31 and quarter replaced by arbitrary functions. The dot
  therefore executes no finishAdd or finishScale call, and no CW kernel.
- Record builders: `finishConcreteField_slots`/`finishConcreteField_W` and `NHE_ops_W`
  (add = finishAdd, W-preserving; mulM31 = finishScale, ok for every input).
- FIn_Install.finishOps and FIn_WeightsInstall.install: `finishOps_round_slots` and
  `finishOps_round_sites` (their round slots are the deployed ones).
- Query dictionaries other than the 094 ones. tx2 NJJ_Common.query runs query_values on
  Dcon (NFW_QueryResume.tx2). `Reach` is the set of tx2 query-loop states reached from the
  resume state by successful steps. `reach_domain` gives NFS_QueryInvariant.Domain at every
  reached state (NID_ResumeQuery.domain, preserved by NFS_QueryInvariant.step).
  `Dcon_values_canon` gives the canonical opening values (SAQ_Decoder.read producer), and
  `tx2_step_sites` gives the circle, line and three tail calls at every reached tx2 state.
  The remaining named dictionaries are installers whose deployed instances carry the
  concrete slots: fill, m0 and NNH_Run5bQuerySlots.model install NJJ_QueryOps.concrete;
  LIBC_QueryLoop.model and NNX_QueryOutput.run run Dsel (094 join); NFS_QueryOps.base,
  SAQ_LineQuery.install, SAQ_QuerySource.install and FIp_Install.select reduce to the
  concrete slots (NHW_DeployedStabilize.deployed). That last classification reads the
  sources and is not a Lean statement.

**NPH_R22JoinCW3 (L036, 9 statements).**
- `concrete_tail_sites`: if the un-installed concrete op3/op2/op9 (SAQ_MixedSource.mulE,
  SAQ_Arithmetic.add/mulK) run at a state with the query invariant, every CW call inside
  receives W arguments. On the deployed paths these slots are replaced (Dcon_tail).
- CurrentPreparedClaim (CurrentClaimDotModel prepared_claim). `ClaimReach` is the set of
  claim-loop states. `claim_body_preserves`/`claim_reach_canon` keep the 7 parts canonical
  along every successful iteration, from `claim_initial`. The coefficients come from the
  concrete powers instance (`claim_powers`). `claim_sites`: at every reached state the
  exit-branch prepared_claim_sum is ok with canonical output, so its CW mul/add receive
  canonical arguments. Producer hypotheses are kept explicit: canonical kappa and inactive,
  and canonical finishDot outputs of the ClaimDotOps.

**CW checklist (NPH_SITES.json): 26 sites, 25 W_LEMMA, 1 NO_CW_CALL, 0 OPEN.** The site-level
lemmas are complete. CW is **not** moved to (b), because two contexts remain open:
1. the claim_sites producer hypotheses at the reached prepare (kappa from the sampler,
   inactive, the installed ClaimDotOps finishDot), and which of the three sum loops the
   deployed prepare executes;
2. the S1ClaimOwnedNestedModelV1 owned_sum and S1ClaimBorrowedAbiNativeV1
   borrowed_abi.owned_sum invariants through owned_claim_loops.

**Counts (220 executed checked or mixed definitions): unchanged.**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 25 |
| precondition proved from the callers (b) | 0 |
| open | 101 |
| NOT_EXECUTED (excluded) | 5 |

Rows exposed: 365 of 396 CLOSED rows still depend on at least one open or domain-only
definition; 31 are served only by TOTAL or DIRECT definitions.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 14a. CW step 3: the deployed claim loop (same run)

Two more scopes: L037 failed because `loop.eq_def` yields a match rather than a bind; the
script was changed to case on the body result, and L038 accepted NPH_R22JoinCW4 (3.71 s,
6,865,628 KiB, swap 0, 6 axiom lines, all standard). 8 of this run's 40 scopes are used.

- The deployed claim is BorrowedClaimPrepared.claim = borrowed_abi.prepared_claim_owned on
  AspisR1S5ClaimDotConcreteAdapter.concreteOps QRaw (RPz7_S1BorrowedClaimPreparedBoundaryV1).
- `sums_eq`: borrowed_abi.owned_sum, owned_sum and prepared_claim_sum are one function (rfl).
  So the three CurrentPreparedClaim sum-loop bodies are served by the same site lemma.
- `owned_body_cont`, `owned_body_done` and `owned_loop_canon`: every successful run of the
  outer owned loop from canonical parts returns canonical parts. This is a fuel induction
  through `loop.eq_def`.
- `concrete_finish`: the concreteOps finishDot output is canonical for every state
  (finishFromPush_total). This discharges the finishDot producer hypothesis for the
  deployed record.
- `owned_claim_sites`: on concreteOps, from a canonical kappa and inactive, the exit-branch
  owned_sum is ok with canonical output.

**CW status.** Every CW site has a lemma, and every CW context but one is composed from
producers. The remaining context is the walk of PreparedScratchModel.prepare
(BorrowedClaimPrepared.boundaries) from its entry to the claim call. That walk would show
that kappa is a PreparedModel.scalar output (producer
AspisR1ClaimPreparedBridge.scalar_candidate_samplers_false_canonical) and that inactive is
the inactive decoder output (producer F3M_InactiveCanonical.source). Until it is composed,
the CW kernels stay domain-only. **Counts unchanged: 67/27/25/0/101 of 220; rows 365 of 396
exposed.**

Not started in this run: SM, QA, SC, R72, FIq and the 345 body walk.

Target not yet established.

## 15. CurrentWide reaches (b); continuation (worker of 2026-11-10, late)

### 15a. CW: the prepare walk to the claim call

Eight scopes were used, L039–L046 (8 of this run's 40). L039–L043 failed on proof-script
details, and each script was changed before the next scope:
- L039: `dsimp` made no progress, and guardedNew had no return type.
- L040 and L041: the rewrite found no claim occurrence.
- L042: a trace probe. It showed that the let-pattern match on (kappa, t2) is reduced only by
  `refine` unification, not by `dsimp`.
- L043: a pair-bind lemma did not unify with the matcher.
- L045: a structure-instance parse error.

L044 accepted NPH_R22JoinCW5 (5.34 s, 6,713,168 KiB), and L046 accepted NPH_R22JoinCW6
(3.92 s, 6,725,872 KiB). Swap was 0 in all eight. All 17 accepted `#print axioms` lines are
within [propext, Classical.choice, Quot.sound], and there is no sorry. The lead decision
holds: no ops interface, merged module or closed-row statement is changed.

**NPH_R22JoinCW5 (L044).**
- `prepare_claim_congr`. Take any PreparedScratchModel.Boundaries B and any claim function c'.
  Suppose c' agrees with B.claim at (v.y1, v.inactive, any scratch, any kappa returned by a
  successful row-28 flag-false PreparedModel.scalar of B.sampling). Then prepare with B.claim
  replaced by c' equals prepare B.
  - This covers every outcome of the later steps and both fold branches.
  - It is the formal form of "every claim call that prepare executes receives such a kappa,
    and inactive = v.inactive".
  - It is proved by bind-stepping through the prepare body.
- `deployed_kappa`. On concreteBoundaries (installedBoundaries S e), every such kappa is
  canonical. installed_as_candidate_samplers (rfl) gives installedBoundaries S e =
  withCandidateSamplers (withSourceFromQm (withConcreteQueries S e)). The producer is then
  scalar_candidate_samplers_false_canonical.
- `originalNew_guarded`. Assume the retained inactive is canonical. Then
  BorrowedClaimPrepared.originalNew S e equals guardedNew S e: the same transported prepare,
  whose claim boundary guardedClaim runs the borrowed claim only when kappa and inactive are
  canonical and fails otherwise.
- `claim_body` (rfl). The borrowed claim is owned_claim_loops on concreteOps QRaw.
- `guarded_claim_sites`. Wherever guardedClaim runs the borrowed claim, kappa and inactive are
  canonical. Then, for every successful powers, initial update and claim loop, the exit
  owned_sum is ok with canonical output (NPH_R22JoinCW4.owned_claim_sites).

**NPH_R22JoinCW6 (L046).**
- `candidate_op8_congr`. Take any Ops O whose op5 is InstalledPreparation.sourceView, and any
  f that agrees with O.op8 on views v with sourceView p s y = ok (.Ok v). Then replacing op8
  by f leaves verifier.candidate.prepare unchanged. So every op8 call that the tx1 prepare
  executes is on a source-view output. The irreducible compact offsets are handled by
  `ls_eq`/`os_eq`/`oy_eq`/`oi_eq`.
- `deployed_prepare_guarded`. Take op5 = sourceView and op8 = originalNew
  (withOriginalSerializer closedSampling) Total.embed. Then candidate.prepare equals the same
  body with op8 := guardedOp8. The inactive comes from F3M_InactiveCanonical.source and the
  kappa from deployed_kappa.
- `installed_op5` (rfl), `installed_op8` (rfl to closedInstall, then
  NNH_Run5bPreparedCore.installed) and `installed_prepare_guarded`. These give the same
  equality for DrvC_Installation.currentInstalled cfg, for every configuration. That includes
  NOC_PrepareFront.cur c, which is what tx1 runs.

**CW moves to (b).** This was the last open CW context. Every executing CW site in
NPH_SITES.json (25 W_LEMMA + 1 NO_CW_CALL) has a limb-bound lemma, and every site context is
composed from producers along the reached body:
- the tx1 094 query path (Join094/Join094Step);
- the tx2 finish and query (CW2/CW3);
- the deployed claim loop (CW4);
- the tx1 prepare to the claim (CW5/CW6).

AspisR1CurrentWide.field CM31.mul, M31.add and M31.sub are now PRECONDITION_B in
NPH_R22_CONE.json. Each keeps its previous judgment under
`nph_judgment_before_20261110_late_cw`.

Two caveats carry over unchanged from section 14:
- NFS_QueryOps.base, SAQ_LineQuery.install, SAQ_QuerySource.install and FIp_Install.select
  are classified as reducing to the concrete slots. That classification reads the sources;
  it is not a Lean statement.
- The NPH_SITES.json checklist is a textual screen. It cannot see calls made through notation,
  instances or callback records beyond the ones traced.

**Counts (220 executed checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 22 |
| precondition proved from the callers (b) | 3 |
| open | 101 |
| NOT_EXECUTED (excluded) | 5 |

**Rows exposed: 363 of 396** CLOSED rows still depend on at least one open or domain-only
definition (was 365). 33 are served only by TOTAL, DIRECT or (b) definitions. The row gain is
small because the CW kernels' rows are also served by SM, QA and FIq kernels and by the
accumulator families.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.
