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

### 15b. SM: the mask site closed; input producers open

One more scope was used: L047, accepted on the first attempt (3.62 s, 5,888,908 KiB, swap 0,
1 axiom line, standard). That makes 9 of this run's 40.

**NPH_R22JoinSM2.FIp_mask_site (L047).** For every seed record, take inputs whose probe
images are canonical: every c1 cell, every mask-only cell, every point cell, and g. Then
(FIp_SemanticArithmetic.install seed).mask is ok, with canonical output. The proof is
NHU_Mask.result, a theorem already in the closure, transported by NHU_Mask.adopted (rfl).
NHU_Mask.result itself proves state_only_selected_mask_value ok and canonical on canonical
inputs. It establishes all the loop invariants and the 27-entry coefficient array through
the closure's coefficient, Horner and linear inductions. So every SM kernel call executed
inside the mask returns ok. In NPH_SITES.json:
- the four loop wrappers (selected_mask_linears_loop and state_only_selected_mask_value_loop0,
  loop1 and loop2) are now SUBSUMED_CANONICAL_TOTAL;
- FIp_SemanticArithmetic.mask is CANONICAL_SITE.

The two SM items "loop compositions" and "coefficient-array invariant" are therefore
discharged at the mask site, without new loop proofs.

**SM is not moved to (b).** The mask is called only from FinishModel.finish
(RPz7_S1SemanticFinishModelV1, the tx1 semantic finish) as `B.mask a a1 q alpha`. These are
still open:
1. canonicality of the arguments at that call:
   - a = B.fromFn 16 closureFn9 claims and a1 = B.fromFn 10 closureFn5 claims;
   - q = claims[0][27];
   - claims comes from the deployed B.claims decoder;
   - alpha is the RoundModel.rounds output;
2. the same for the later B.mul challenges.eta val2, B.add mask q1 and B.add q2 val3[28];
3. a Lean identification of the deployed B (IDa_Deployed.boundaries r) with
   FIp_SemanticArithmetic.install. NNG_InstallArithmetic defines the transported add/mul;
4. the right operands of qm31_sum_products3_prepared (loop0 callers, FJe_Sum3IndexBridge.old
   and the PoseidonPreparedIndex* loops).

NHS_FinishFields.source is a success-only inversion of FinishModel.finish, so it does not
serve as a reach statement. The method that closed CW applies unchanged: a congruence
theorem on FinishModel.finish with a guarded mask/add/mul boundary, plus producer lemmas
for claims and alpha. The producers were not located in this run.

**Counts: unchanged since 15a.** 67/27/22/3/101 of 220; rows exposed 363 of 396.

Not started in this run: QA, SC, R72, FIq and the 345 body walk. 31 of the 40 scopes remain
unused.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

## 16. Paused (owner pause relayed by the lead, 2026-11-10)

No scope was launched in this run. NPH_COMPILE.tsv still ends at L047, and 31 of the 40 scopes
are unused. NPH_R22_CONE.json and NPH_SITES.json are unchanged. Counts stay at
67/27/22/3/101 of 220, with 363 of 396 rows exposed. SM is not at (b).

**Producers located for the SM finish join (source reading only; not yet composed in Lean).**
1. The deployed B slots. IDa_Deployed.boundaries r sets mask/add/mul :=
   FIp_SemanticArithmetic.mask/add/mul. The tx1 op9 slot runs S1SemanticInstallation.verify
   children (ClaimsUnrolledFinish.install (calls r) (IDa_Deployed.boundaries r))
   (NOC_Op9Slot.slot, rfl). So the tie to FIp_SemanticArithmetic.install should be rfl
   (item 3).
2. alpha: SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical. It holds for
   any RoundModel.Boundaries on a successful rounds call. Its predicate is
   ExtractedMaskTowerAdd.CanonicalQM ∘ toSelected, and toSelected has the same shape as
   toProbe.
3. claims: ClaimsUnrolledFinish.claims_value, then FJa_ClaimsReference.reached (gives
   decodeRows on the same record), then LIB_VClaimsCanonical.source_canonical (gives
   decodeMain_success_members_canonical) on each of the three rows.
4. fromFn: OraclePortStdBuilder.fromFn/fromFnLoop. A short induction is still needed: if every
   successful call_mut output satisfies Q, then every array element does.
   closureFn6/closureFn2 return val1[0][i] and val1[0][16+i].
5. val3 = R.decode 29 vr 87: decodeMain_success_members_canonical
   (RawActualDecodeKMainAdapter).
6. eta and the terminal inputs: FJn_BeginCanonical.value (the successful r1_wire.begin in
   VerifyPrefix.verify). So the congruence must start at VerifyPrefix.verify, not at
   FinishModel.finish alone.
7. val2 = terminal output: NLU_Terminal.source gives a canonical output under
   NLU_Terminal.InputDomain pub c, plus canonical claims and alpha. InputDomain also needs the
   public digest domain and asset_id < P. Those come from pub, not from begin. Their producer
   has not been located. **This is the one SM input whose bound has no located producer
   yet.**

**Exact next step.** Write NPH_R22JoinSM3, in four parts:
- `finish_congr`: bind-stepping in the style of NPH_R22JoinCW5.prepare_claim_congr, with
  mask/add/mul replaced by functions that agree at the reached arguments;
- `verify_congr` over VerifyPrefix.verify, which supplies the begin challenges;
- the producer lemmas 2–5;
- a guarded B whose mask/add/mul run only on canonical (or W) arguments.

Then locate the producer for item 7 (public digest domain and asset bound), or report it as a
site without a producer. After that comes item 4 of section 15b (the
qm31_sum_products3_prepared right operands). Tasks 2 and 3 of the brief (the four query
installers as Lean statements; QA, SC, R72, FIq and the 345 walk) were not started.

No reachable input on which the wrapping binary accepts and the checked model rejects was
found. Target not yet established.

## 17. SM finish context composed; four query installers as Lean statements (continuation worker, 2026-11-10, after the owner pause)

Twenty scopes were used, L048–L067, of this run's 40 (NPH_COMPILE.tsv records every one). Each
ran at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, with lean -j1 -M7000 and a
180 s timeout. Swap was 0 in every scope. No cap was raised, and no failed shape was rerun
unchanged.

**The L048–L060 timeouts and their fix.** The first finish congruence timed out three times
(L048–L050), stalled at MemoryHigh: about 23 s of user CPU, 16% CPU, no major page faults,
and a cgroup peak of 6.6–6.8 GB.
- L051 split the module and showed that `finish_congr` is the cause.
- L055–L059 were uncredited diagnostics (bisection with `sorry`, then progress markers
  written to a file in the attempt directory). They showed that elaborating the statement
  alone hangs, and that the hang starts at the fourth hypothesis: 15 binders and 13 premises
  in one ∀-chain.
- L060 showed that bundling the reached premises into three `def` predicates elaborates in
  0.38 s, while the original form still hangs with all linters off.
- The cost therefore grows with the depth of the premise chain, not with the proof or a
  linter. The accepted statement uses the bundled form.

**Accepted modules (standard axioms only, no sorry):**

| Scope | Module | Wall | Peak RSS (KiB) | Axiom lines |
|---|---|---:|---:|---:|
| L054 | NPH_R22JoinSM3 | 1.97 s | 3,841,916 | 11 |
| L061 | NPH_R22JoinSM3F | 2.78 s | — | 1 |
| L063 | NPH_R22JoinSM4 | 3.84 s | 6,674,812 | 18 |
| L065 | NPH_R22JoinSM5 | 3.05 s | 6,742,856 | 4 |
| L067 | NPH_R22Installers2 | 3.07 s | 5,910,312 | 8 |

- NPH_R22JoinSM3 holds the helpers and the verify congruence:
  - `verify_congr`: VerifyPrefix.verify F = VerifyPrefix.verify F' whenever F and F' agree at
    the prefix, transcript and challenges returned by the SAME successful parse, public
    transcript and begin calls;
  - `fromFnLoop_mem`/`fromFn_mem`: the induction over OraclePortStdBuilder.fromFnLoop.
    Every element of a successful fromFn output is a call_mut output on the unchanged
    capture;
  - `closure9_mem`/`closure5_mem`: closureFn6 and closureFn2 return an element of claims[0];
  - `idx_mem`, `branch_cont`, `map_err11_cont`, `circle_eq`.
- NPH_R22JoinSM3F holds `finish_congr`. FinishModel.finish with mask, add and mul replaced
  equals the original whenever the replacements agree at the arguments the finish passes, on
  the SAME successful earlier calls:
  - Head: rounds and claims;
  - Fill: the two fromFn calls and claims[0][27];
  - the Ok terminal output;
  - the mask and mul outputs;
  - Tail: the first add, the row-25 record, its decode and entry 28.
  The proof bind-steps every outcome of every later step.
- NPH_R22JoinSM4 holds the producers and the guarded record.
  - `Bd std r` is S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std
    (IDa_Deployed.boundaries r)).
  - `deployed_slots` and `deployed_install` (rfl) give the deployed mask/add/mul as
    FIp_SemanticArithmetic.mask/add/mul. Bd is definitionally FIp_SemanticArithmetic.install
    of itself, which settles item 3 of section 15b.
  - `Bg` runs FIp mask only on canonical cells and FIp add/mul only on canonical operands,
    and fails otherwise.
  - Producers: `claims_canon` (claims_value, then FJa_ClaimsCanonical.value, for every
    claims cell); `alpha_canon` (verifier_round_alpha_canonical); `fromFn9_canon`,
    `fromFn5_canon` and `cell_canon`; `decode_canon` (decodeMain_success_members_canonical);
    `terminal_canon` (NLU_Terminal.source under InputDomain); `mask_out_canon`
    (NPH_R22JoinSM2.FIp_mask_site). The mul and first-add outputs come from
    FIp_SemanticValues.mul/add.
  - `deployed_finish_guarded`: finish over Bg = finish over Bd, given a canonical eta and
    NLU_Terminal.InputDomain.
  - `deployed_verify_guarded`: verify over the Bg finish = verify over the Bd finish for
    every public with LIB_VPublicDomain.publicDigestDom. Inside, the begin challenges come
    from FJn_BeginCanonical.value, and the asset half of InputDomain comes from
    LIB_VPublicAsset.bytes_asset at the public_bytes of the SAME successful public transcript
    (PreparationSuccess.public_transcript_success).
  - Site lemmas `guarded_mask_site`, `guarded_add_site` and `guarded_mul_site`: wherever Bg
    runs a kernel, its arguments are canonical, and the kernel is ok with a canonical (mask)
    or W (add/mul) output.
- NPH_R22JoinSM5 holds `slot_guarded`. For every host context and every public pub with
  publicDigestDom (toRetainedPublic pub), the literal installed op9 slot on release `none`
  equals S1SemanticInstallation.verify over `Bslot`, the Claims-unrolled deployed record
  with the guarded mask/add/mul. The proof is NOC_Op9Slot.slot, then bd_eq/bg_eq (rfl), then
  deployed_verify_guarded. The deployed boundary tie is rfl, as section 16 expected.
- NPH_R22Installers2 replaces the source reading of section 14.
  - For NFS_QueryOps.base, SAQ_QuerySource.install, SAQ_LineQuery.install and
    FIp_Install.select, every CW-executing query slot the installer sets (op2, op3, op9,
    op16, op17, op20) is the NJJ_QueryOps.concrete slot. Every other slot passes through.
  - Each installer applied to concrete returns concrete (fip_select_concrete: whenever the
    configuration's query is concrete).
  - **The section 14 caveat on these four installers is removed.** The other caveat stands:
    NPH_SITES.json is a textual screen.

**SM is not moved to (b).** Two SM contexts remain open.
1. **The digest-domain premise of `slot_guarded`.** This is the one SM input whose bound has
   no composed producer. val2, the Ok terminal output that enters `B.mul challenges.eta
   val2`, is canonical only under NLU_Terminal.InputDomain. Every field of InputDomain is now
   produced inside the verify except the digest half, publicDigestDom of the public the op9
   slot receives.
   - Its producer is at 345: NOM_TerminalDomain.validated_digest, at the installed op21
     validate's success on the decoded statement, carried by NOC_Stage1Forward.publicBinding
     and NOC_Op9Slot.pub_round.
   - The call path from that validate to the slot is located: stage1_owned →
     first_decoded (sp) → (S c).op10 = NIS_Tx1Boundary.release (at_none, rfl) →
     NHL_EmittedTx1.tx1 → prepareCall → NHL_EmittedPrepare, which calls ops.op9 at its own
     public1 with obs from tx1. This is not yet composed.
   - Every layer except stage1_owned passes the public through unchanged, so those layers
     need only a rewrite congruence. stage1_owned needs a bind-stepping walk from the op21
     success to the first_decoded call. Its premises must be bundled, given L055–L060.
2. **The qm31_sum_products3_prepared right operands** (loop0 callers FJe_Sum3IndexBridge.old
   and the PoseidonPreparedIndex* loops), unchanged from section 15b.

**Counts: unchanged.** 67/27/22/3/101 of 220; rows exposed 363 of 396. NPH_SITES.json records
the new SM contexts and the installer statements. NPH_R22_CONE.json keeps every judgment and
records the SM context note on the five SM kernels.

Not started in this run: QA, SC, R72, FIq and the 345 body walk. 20 of the 40 scopes remain.

No executing site was found that passes a value whose bound no producer gives, other than the
digest-domain premise named above, whose producer is located and only the tie is missing. No
reachable input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 17a. SM: the digest premise carried to tx1; sum3 SM copy proof-only (same run)

One more scope was used: L068 accepted NPH_R22JoinSM6 on the first attempt (3.27 s, 6,749,108
KiB, swap 0, 11 axiom lines, all standard). That makes 21 of this run's 40.
- `prepare_op9_congr` and `tx1_op9_congr`: verifier.candidate.prepare and verifier.candidate.tx1
  are unchanged when op9 is replaced by any f that agrees with op9 at the candidate's OWN
  public. The other arguments are free. The irreducible constants (LOGICAL_SEMANTIC,
  OFF_SEMANTIC, OFF_Y1, OFF_INACTIVE, ZERO, OFF_FOLDED_ROOT, OFF_ROUND1) do not read op9.
  So the candidate reads op9 only at its own public.
- `digest_of_binding`: take a statement whose installed op21 validate returned Ok, and a
  current public cp equal to toCurrentPublic of that statement's library semantic public.
  Then publicDigestDom (toRetainedPublic cp) holds (NOC_Op9Slot.pub_round, then
  NOM_TerminalDomain.validated_digest). NOC_Stage1Forward.publicBinding states exactly this
  equality for the semantic public sp that stage1_owned computes, and fdLemma unfolds
  first_decoded (S c) sp to this tx1 at that public, with hash () and obs none.
- `tx1_guarded`: at every host context, for such a public, the deployed tx1 candidate equals
  the same tx1 whose op9 slot on release `none` is the guarded semantic installation over
  NPH_R22JoinSM5.Bslot.

**SM sum3 right operands: not executing.** NPH_SUM3_REFS.json (NPH_sum3_refs_host.py, a
read-only scan of the replayed src) lists every reference to the SM-copy
qm31_sum_products3_prepared/_loop0 and to the model loops that call it. Apart from the
copy's own definitions, every reference is one of two kinds:
- nine proof-module abbrevs (the RPv_*Poseidon*Loop* and FJe_Sum3*Bridge Loop/old/native
  abbrevs), which are themselves referenced only from theorems;
- theorems.

The executing sum3 is FIq_Native.field.qm31_sum_products3_prepared, in the FIq family
(FJe_Sum3WrapperBridge.same relates the two copies). Under lead ruling 1 (proof-only
references, the R65/R66 precedent), the SM site qm31_sum_products3_prepared_loop0 is
NOT_EXECUTING. This is a textual screen, like the rest of NPH_SITES.json.

**SM is still not moved to (b).** Every SM context is now composed or excluded except one
link. stage1_owned must call first_decoded only at the semantic public of a statement whose
op21 returned Ok. In the source this is the order of the body: op47 decode, then op21, then
semantic_public, then first_decoded, in both data branches. NOC_Stage1Forward.body states it
only as hypotheses, so it is not a Lean statement. Closing it needs a congruence over
r1_pool_adapter.owned.stage1_owned (two branches of about 35 binds, with bundled premises
after the lesson of L055–L060) and the record identity from (S c).op10 to the candidate tx1
(the generic first steps of fdLemma). This is the first piece of the 345 body walk.

**Counts: unchanged.** 67/27/22/3/101 of 220; rows exposed 363 of 396.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 17b. QA powers context, SC and R72 (same run)

Four more scopes were used: L069, L070–L071 and L072. That makes 25 of this run's 40. All accepted
modules use standard axioms only, with no sorry. L070 failed on one wrongly qualified lemma name,
and the name was changed before L071.

| Scope | Module | Wall | Peak RSS (KiB) | Axiom lines |
|---|---|---:|---:|---:|
| L069 | NPH_R22JoinQA2 | 3.11 s | 6,724,284 | 2 |
| L071 | NPH_R22JoinSC1 | 2.76 s | 5,620,868 | 8 |
| L072 | NPH_R22R72 | 1.98 s | 5,217,312 | 2 |

**QA: the "CurrentWideMul WideExact.mul callers" context is closed (NPH_R22JoinQA2).**
- The site's only direct caller is AspisR1PowersConcreteMul.sourceMul. Its only executing
  caller is AspisR1LoopPowers.field.WideExact.mul, inside weights.early_powers_loop.body.
- early_powers has exactly two executing callers (NPH_POWERS_REFS.json):
  - ClaimPowers.powers, the concreteOps claim powers slot. `claim_powers_ok`: ok on a
    canonical kappa, which NPH_R22JoinCW5.guarded_claim_sites gives at every executed claim.
  - Tx2N_Powers.powers, the tx2 stage op17 slot. `tx2_powers_ok`: ok at p.gamma of the
    Prepared that the tx2 resume returns (gamma canonical from
    NPH_R22JoinCW2.entered_domain). tx2_common calls op17 only as op17 29 p.gamma.
- early_powers is ok on canonical input, so every WideExact.mul call it executes returns ok.
- QA is still not (b). Two contexts remain: the installer contexts outside 094, and NFN
  op14/op15 under NFN_NEA_FieldProduct.ops.

**SC moves to (b) (NPH_R22JoinSC1).**
- `step_congr` and `rounds_congr`: RoundModel.step and rounds are unchanged when boundary and
  value are replaced by functions that agree with them on the arguments the step actually
  passes. Those arguments are:
  - the Ok decode(28) coefficients;
  - the alpha array returned by the SAME successful Array.update with the Ok
    semantic_validated value;
  - the round.

  rounds is unrolled over rounds 0..9.
- `deployed_rounds_guarded` has NO premise: rounds over `Rg` equals rounds over
  AspisS1ExtractedRoundChildren.children. `Rg` runs generatedMainBoundary/Value only on
  canonical coefficients, and value only for round < 10 with a canonical alpha[round].
  - Producers: decodeMain_success_members_canonical, and
    semantic_success_selected_canonical through `update_at` (NHI_ArrayCells).
  - `finish_rounds_guarded` gives the same inside FinishModel.finish.
- Site lemmas `guarded_boundary_site` and `guarded_value_site`: wherever Rg runs an entry, the
  whole entry call is ok with canonical output (JFv_RoundArithmetic.boundary/value). So every
  SC kernel call inside it returns ok.
- NJM_RoundJoin.R is children by definition. The other referrers are proof-only
  (NPH_SC_REFS.json through NPH_SC_REFS4.json):
  - the RawGeneratedSemanticRoundPolynomialAdapter copy is used only by actualRoundBoundaries,
    inside a Prop, a structure and theorems;
  - NJM_RoundJoin.afterSemantic is used only under model definitions that take a parse
    proof as an argument;
  - NJM_RoundRoot.Cases is used only from the unreached NJM_RoundsClosed.Child;
  - NNG_LegacySuffix136.f_r is used only from theorems.
- Moved to PRECONDITION_B: SemanticCallExtraction CM31.mul, M31.add, M31.sub, and
  r1_semantic.semantic_value_loop.body (previously OPEN: CALLER_DOMAIN_NOT_COMPOSED; it runs
  only inside the guarded semantic_value_entry). Previous judgments are kept under
  `nph_judgment_before_20261110_sc`.
- **The proof-only classification of the non-deployed referrers is a textual screen, and I
  flag it for lead review.**

**R72 moves to (b) (NPH_R22R72).**
- Every reached R72 kernel call lies inside AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
  (definition-level scan NPH_R72_REFS.json, plus the deployed_splitB REACHABLE list). Its
  reached callers are the wrapper externals:
  - the root-namespace circle.secure_ood_circle_point_from_parameter;
  - the AspisR1CircleFallback copy, reached through root transcript.circle_fallback_point and
    then AspisR1CircleFallback.transcript.circle_fallback_point.

  Both run only inside AspisR1CircleSampleWrapper.sampler.circle_sample (its mapper and its
  fallback closure). The R72-internal transcript loop is not reached.
- `circle_sample_total`: circle_sample is ok for EVERY input
  (RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle). So every executed
  R72 kernel call returns ok, whatever its caller passes. `circle_source_total` states the same
  for the deployed finish circle boundary F3M_CircleSource.source.
- Moved to PRECONDITION_B: AspisR72Sampler CM31.mul, CM31.square, M31.add, M31.neg and M31.sub.
  Previous judgments are kept under `nph_judgment_before_20261110_r72`. AspisR72Sampler
  r24_canonical_mul stays OPEN: NO_FROZEN_COUNTERPART.

**Counts (220 executed checked or mixed definitions):**

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 14 (was 22) |
| precondition proved from the callers (b) | 12 (was 3) |
| open | 100 (was 101) |
| NOT_EXECUTED (excluded) | 5 |

**Rows exposed: 359 of 396** (was 363). These are the CLOSED rows that still depend on at least
one open or domain-only definition; 37 rows are served only by TOTAL, DIRECT or (b)
definitions. The recount script reproduces the recorded 363 before the change.

Families at (b): CW, SC and R72. Not at (b):
- SM: one link open, the stage1_owned ordering of 17a.
- QA: two contexts open.
- FIq: 238 sites, not started.

The 345 body walk is not started; its first piece is the SM link.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found. 15 of the 40
scopes remain unused.

Target not yet established.

## 18. SM reaches (b); continuation (worker of 2026-11-10, after L072)

Every scope in this run ran at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, with
lean -j1 -M7000 -DElab.async=false and a 180 s timeout. NPH_COMPILE.tsv records every one.
Swap was 0 throughout. No cap was raised, and no failed shape was rerun unchanged. The lead
decision holds: no ops interface, merged module or closed-row statement is changed.

### 18a. SM: the stage1_owned ordering link

Two scopes were used, L073 and L074 (2 of this run's 40).
- L073 failed in two places, and both were changed before L074.
  - `stage1_congr` stopped in both branches at the bind of the irreducible
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES. Unification cannot see through it to equate the
    two records. The constant is now unfolded at that step.
  - `G_agree` hit a whnf heartbeat timeout. `rw [NNH_Run5bCurrentInventory.adapter]` tried to
    unify `G ?c` with the deployed sdk record. It was replaced by explicit `Eq.trans` steps
    and a small `current_congr` lemma.
- L074 accepted NPH_R22JoinSM7: 4.45 s, 6,782,664 KiB, swap 0, 11 `#print axioms` lines, all
  within [propext, Classical.choice, Quot.sound]. There is no sorry.

**NPH_R22JoinSM7 statements.**
- `stage1_congr` holds for every adapter Ops record `ops` and every record `f`. Suppose f.op10
  agrees with ops.op10 at every public p that is `Validated ops p`, meaning p is the
  semantic_public of a statement whose ops.op21 returned Ok. Then
  r1_pool_adapter.owned.stage1_owned over `{ ops with op10 := f.op10 }` equals stage1_owned
  over ops, for every program, account slice and instruction data.
  - The proof bind-steps both data branches of the extracted body ([3,10] and [3,11]).
  - In each branch the only first_decoded call is at `p ← semantic_public val2`, after
    `ops.op21 val2` returned Ok (`ok_of_map_err` inverts the map_err and branch).
  - The premise is bundled into the def predicate `Validated`, following the L055–L060
    lesson. The statement has four binders and one premise.
- `fd10`: first_decoded reads op10 only at its own public, bytes, proof and split, with hash
  () and observer none.
- `slotM`, `slotM_guarded` and `tx1_guardedM` restate the SM5/SM6 slot and tx1 statements for
  the record that the deployed adapter actually runs. That record is
  NNH_Run5bCurrentShape.current m env err r, the one in NOC_Stage1Forward.fdLemma. SM5 and SM6
  were stated for DrvC_Installation.currentInstalled (configuration c), which is a different
  configuration term.
  - `slotM` is rfl for every m, env, err and r. The boundaries and std of that configuration
    depend only on the reservation (IDa_Deployed.selected_fields).
- `G c` is NOC_Stage1Forward.S c with one change: op10 on observer `none` runs the tx1
  candidate over `Og c`, whose op9 slot on release `none` is the guarded semantic installation
  over NPH_R22JoinSM5.Bslot. In Bslot, mask, add and mul run only on canonical arguments.
  - `G_op10_none` and `Og_op9_none` (both rfl) state this.
  - Every other slot of G c is that of S c.
- `G_agree`: at every Validated public, G c's op10 equals S c's op10. The proof chains
  NOC_Stage1Forward.publicBinding, the rfl op21 = NNH_S1HostCodec.validate (as in ok345),
  NPH_R22JoinSM6.digest_of_binding, NNH_Run5bCurrentInventory.adapter, current_congr and
  tx1_guardedM.
- `stage1_guarded` has **no premise**. For every host context c and every input,
  stage1_owned (G c) program xs data = stage1_owned (S c) program xs data.

**Call chain (textual screen of the extracted sources; flagged for lead review):**
- op9 is read once, in verifier.candidate.prepare (CurrentCompactCallerModelV1).
- prepare is called once, from verifier.candidate.tx1.
- tx1 is reached through op10 = AspisS6CurrentFirstInstallation.current
  (NNH_Run5bCurrentInventory.adapter).
- op10 is read once in AdapterRwModel, by first_decoded.
- first_decoded is called twice, both times in stage1_owned.

So every op9 execution of the deployed 345 entry is an execution inside G c's guarded
installation.

**SM moves to (b).** Every executing SM site in NPH_SITES.json has a limb-bound lemma: 28
W_LEMMA, 2 EVERY_INPUT, 1 CANONICAL_SITE and 4 SUBSUMED_CANONICAL_TOTAL. Every site context is
composed from producers along the reached body:
- the tx1 094 query path (3 JOINED_094);
- the tx2 query tail (NPH_R22JoinCW2.tx2_step_sites);
- the tx1 semantic finish (SM4–SM7, now down to the 345 entry).

The SM-copy sum3 site stays NOT_EXECUTING. That classification rests on NPH_SUM3_REFS.json, a
textual screen, and is flagged. Moved to PRECONDITION_B: AspisR1SelectedMaskProbe CM31.mul,
CM31.square, M31.add, M31.neg and M31.sub. Their previous judgments are kept under
`nph_judgment_before_20261110_sm7`.

NPH_recount.py recounts the cone. It reproduces the recorded 67/27/14/12/100 and 359 before the
change. NPH_move_family.py performs the move and the recount.

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 9 (was 14) |
| precondition proved from the callers (b) | 17 (was 12) |
| open | 100 |
| NOT_EXECUTED (excluded) | 5 |

**Rows exposed: 328 of 396** (was 359). 68 rows are now served only by TOTAL, DIRECT or (b)
definitions.

Families at (b): CW, SC, R72 and SM. Not yet at (b): QA (two contexts) and FIq (238 sites).

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 18b. QA reaches (b)

Three scopes were used, L075–L077 (5 of this run's 40).
- L075 failed in three places, and each was changed before L076.
  - In `mul_lt`, a rewrite could not see through the `QAmul` abbrev. Its dependents inherited
    the error.
  - `NOC_QueryLink.Dcon` does not exist. The name is `NPH_R22Join094.Dcon`.
  - The configuration-geometry rfl hit whnf timeouts.
- L076 accepted 21 of 26 statements. It also showed that the configured geometry is **not**
  the seed's `NFN_NEW_GeometryDictionary.adopted`: Rc5_Install.seed passes through
  SAQ_CompleteInstall.select, which replaces it by `SAQ_Constructor.install err g`. The
  per-layer rfl through NNH_Tx2Configuration.select timed out in isDefEq, by argument
  congruence on the adapter. These statements were changed to slot facts of
  SAQ_Constructor.install over an abstract inner record, unfolded with dsimp only.
- L077 accepted NPH_R22JoinQA3: 4.13 s, 6,710,132 KiB, swap 0, 25 `#print axioms` lines, all
  standard, no sorry.

**What NPH_R22JoinQA3 proves.** The QA kernels sit behind installer callbacks. Every QA call
those callbacks make in the executed query and geometry bodies receives W arguments, for
**every** input of the body. The call patterns come from a textual screen of
Port3_NativeQueryBody and Port3_NativeGeometryBody, which is flagged.

- **Query.**
  - op6 and op8 are called only in the node pattern `op7 z z; op8; op6 · one`. That pattern
    occurs in query_values and in accumulate_batched_with_node_loop0.body. In the latter,
    `one` is the op5 output, passed unchanged through the loop.
  - The other op7 call (`op7 m node`) is M31.mul, which is TOTAL.
  - `query_sites` covers any record with op7 = M31.mul and W-preserving op6/op8.
  - It is instantiated by `Dcon_sites`, `Dsel_sites` and `NBF_sites` (any NBF-installed
    record).
  - `t2_sites` gives the same for S7Kani3BasisOuter.t2, the context of basis_levels_owned and
    levels.
- **Geometry.**
  - `fip_geometry` (dsimp only through FIp → Rc5 → Rc3 → SAP → release → Rc2.select →
    Rc5.seed → SAQ_CompleteInstall.select → CPP_Install): the configured geometry of every
    FIp-installed configuration is SAQ_Constructor.install err g.
  - `constructor_slots`, `fip_slots`, `cfg_slots` (the S c configuration) and `host_slots`
    (the host-context configuration): that record has op7 = ok 1, op8 = QA sub, op9 = QA mul,
    op10 = QA double, op14 = SAQ_Geometry.line and op15 = SAQ_Geometry.point, whatever g is.
  - `terminal_slots`: Port5Q1_GeometryTerminal.install keeps those slots. That is the record
    Tx1Q_PrefixInstall.geometryBody runs.
  - `stage_geometry_sites`:
    - for every x, the pattern `op9 x x; op10; op7; op8` passes W arguments to QA double and
      QA sub;
    - for every fibre index, op14 and op15 are ok with W output, or the TABLE_B read is out of
      bounds. That read is bounds-checked in both profiles, and no QA call executes.
  - op8 and op10 occur only in that pattern. The suffix-loop op9 is M31.mul, which is TOTAL.
  - `geometry_triple_W` gives the pattern for any GeometryM31W record whose op9 is M31.mul.
    `SAQ_install_sites` and `NFN_install_sites` instantiate it.
- **NFN op14/op15 under NFN_NEA_FieldProduct.ops.**
  - `nea_fibre_point_W`: the NEA fibre point is a FIo_Native CM31 product of canonical table
    entries (NFN_NEA_FieldProduct.geometric_cm), or an out-of-bounds read. It runs no QA
    kernel.
  - `nea_line_W`: line_node then runs the R17 M31 mul/double/sub (QA) on W arguments.
- The WideExact.mul context was closed by NPH_R22JoinQA2 (17b).

**QA moves to (b).** Every QA site has a lemma (23 W_LEMMA, 1 EVERY_INPUT), and every context
is composed. Moved to PRECONDITION_B: AspisR1Qm31ArithmeticProbe CM31.mul, M31.add and M31.sub.
Their previous judgments are kept under `nph_judgment_before_20261110_qa3`. Three items rest on
textual screens and are flagged for lead review:
- the call patterns of the two bodies;
- the executed query dictionaries (Dcon/Dsel, section 14 plus NPH_R22Installers2);
- the geometry stage path.

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 6 (was 9) |
| precondition proved from the callers (b) | 20 (was 17) |
| open | 100 |
| NOT_EXECUTED (excluded) | 5 |

**Rows exposed: 309 of 396** (was 328). 87 rows are served only by TOTAL, DIRECT or (b)
definitions.

Families at (b): CW, SC, R72, SM and QA. The six remaining domain-only definitions are FIq
kernels.

No executing site was found that passes a value whose bound no producer gives. No reachable
input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 18c. FIq: obligation located, not started as proofs; a failed screening approach

No Lean scope was used for FIq. The run's scope total stays at 5 of 40.

**The executing FIq core.** By textual reading, the FIq kernels execute inside the `terminal`
slot of the tx1 semantic finish. IDa_Deployed.boundaries sets terminal := FIq_Terminal.terminal,
which runs FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31. Three parts
of FIq_Native sit inside it:
- the pair-forest semantic terminal (52 of the 121 in-family sites);
- the copy terminal (20);
- the state-only Poseidon oracle and its rounds (about 25).

The remaining in-family sites are the QM31/CM31 tower and the prepared multiplier. NPH_R22Towers
already proves the tower W-lemmas. The prepared-multiplier family is not covered.

**What is missing.** The terminal must be shown total on NLU_Terminal.InputDomain with canonical
claims and alpha. Those are the inputs the SM work already establishes at every executed finish
(NPH_R22JoinSM4.deployed_verify_guarded). No theorem in the closure gives this.
- NLU_Terminal.source concludes `Outcome`, which is success-only: fail maps to True.
- NLH_CompRoot.source, NLH_PartsRoot.source and NLH_WrapperRoot.source each carry an explicit
  `fail err` branch.

So no FIq kernel call is yet shown to receive W arguments at its executing sites. The four FIq
kernels stay domain-only. The proof campaign is a W-invariant through:
- the Poseidon permutation (round-constant add loops, pow5, the internal and external linear
  layers);
- the absorption of public-digest and claim lanes;
- the digest-binding, value-lane, occupancy and path loops of the terminal.

Each producer is available: the canonical claims and alpha, the public digest domain
(NKR_DigestChildren.Domain), asset_id < P and the canonical challenges. They are not yet
composed through those bodies.

**Failed approach, kept as a record.** NPH_fiq_reach_host.py (output NPH_FIQ_REACH.json) is a
read-only forward reachability scan over definition bodies. It starts from the adapter program
and the deployed configuration records and reuses the NPH_sites_scan2 name resolution. It ran on
the host in a capped scope.
- Result: 122 of the 238 FIq sites are forward-reachable. Those are the 121 in-family sites and
  FIq_Terminal.terminal. The 116 alias and outside sites, such as the RPv_FIx/FIy/FJ* `.run`
  models, are not.
- The scan **under-approximates execution**. It also reports NBO_FieldSemantics add/product/
  power and NBF_BasisInstall.install as unreachable, yet NPH_R22Join094 proves the deployed
  Dcon/Dsel run them. In this proof architecture the deployed path is tied to the installed
  records partly through theorems (NOC_QueryLink.values_eq and others), not only through
  definition references.
- It therefore **cannot support any NOT_EXECUTING classification**, and none was made from it.
  The 116 FIq model sites stay OPEN.
- A sound classification needs a reachability notion that follows those theorem-level ties.
  That is a question for the lead.

**The other two domain-only definitions** are AspisR1CanonicalQRawUnified and FIo_QRaw
canonical.Q.raw, with 121 rows each. They are called from the TX2 dot/push raw path
(NHE_DotRaw, FJf_DotPushValue, FIo_NativeExternal). Section 11 recorded that the producer for the
dots output, FIp_DotsOutputCanonical.all, lies outside the L187 closure. Their caller join is not
attempted here.

Counts are unchanged since 18b: 67/27/6/20/100 of 220; rows exposed 309 of 396.

Target not yet established.

## 19. FIq reaches (b): the terminal never fails on its input domain (continuation worker, 2026-11-10, after L077)

Every scope in this run ran at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, with
lean -j1 -M7000 -DElab.async=false and a 180 s timeout. NPH_COMPILE.tsv records every one. Swap
was 0 throughout. No cap was raised, and no failed shape was rerun unchanged. The lead decision
holds: no ops interface, merged module or closed-row statement is changed. The host screens ran
read-only in their own scopes (MemoryHigh 3G, MemoryMax 4G, MemorySwapMax 0, TasksMax 64).

### 19a. The terminal invariant (NPH_R22FIqTerminal, L078)

L078 accepted the module on the first attempt: 3.01 s, 6,451,476 KiB, swap 0, 5 `#print axioms`
lines, all within [propext, Classical.choice, Quot.sound], no sorry.

The W-invariant campaign planned in 18c (one lemma per Poseidon round, linear layer and lane loop)
was not needed. The closure already proves every part of the terminal ok on its domain except one
child, and that child is total for every input:
- NLH_CompRoot.source carries a fail/div branch only for `validate_transition`.
  NHU_TransitionTotal.result (in the replayed closure) proves validate_transition ok for **every**
  public.
- With that, NLH_CompTailFold.source returns `ok (Ok final)` for the whole composition tail: the
  gathers, selectors, Poseidon selectors, the state-only Poseidon oracle and its rounds, the semantic
  absorption, h1, the variant, the copy terminal, the prepared products, the 28 Horner steps and g.
  It also gives canonical composition, h and active.
- NKR_TermTail.result gives the arithmetic suffix ok, and NLH_TermWrapperFactor.source gives the
  84-cell gather, the semantic public and the map/map_err arms.

Statements:
- `composition_ok`: composition_parts is ok, with canonical outputs on Ok. The invalid-amount branch
  is NLH_TermAmount.rejected.
- `parts_ok`: terminal_parts is ok.
- `qm31_ok`: terminal_qm31 is ok on the digest domain, asset_id < P, canonical claims, point and
  challenges.
- `terminal_total`: on NLU_Terminal.InputDomain pub c with canonical claims and alpha,
  FIq_Terminal.terminal pub claims alpha c = ok out for some out. The result is an Ok value or an
  Err rejection, never Aeneas fail or div. So every checked FIq operation the terminal executes
  returns ok, including every call of the four FIq kernels.
- `deployed_terminal` (rfl): (IDa_Deployed.boundaries r).terminal = FIq_Terminal.terminal.

### 19b. Composed to the deployed 345 entry (NPH_R22JoinFIq, L079–L080)

L079 failed on one goal. In `finish_term_congr`, the last goal after `rw [hterm]` is the same bind
up to structure-update projections, and the rewrite's rfl did not close it; dependents inherited
the error. An explicit `rfl` was added. L080 accepted the module: 3.37 s, 6,766,868 KiB, swap 0,
12 axiom lines, all standard, no sorry.
- `finish_term_congr` (generic): FinishModel.finish with the terminal replaced by t' equals the
  original whenever t' agrees at the public, the claims of the SAME successful claims call and the
  alpha of the SAME successful rounds call (NPH_R22JoinSM3.Head).
- `gterm` runs FIq_Terminal.terminal only on `TermDom` (InputDomain, canonical claims and alpha),
  and fails otherwise. `term_site`: wherever gterm runs the terminal, the terminal is ok.
- `deployed_finish_guardedT` and `deployed_verify_guardedT` reuse NPH_R22JoinSM4: claims_canon,
  alpha_canon and the InputDomain built from FJn_BeginCanonical, LIB_VPublicAsset.bytes_asset and
  the digest premise.
- `BslotT r` = NPH_R22JoinSM5.Bslot r with terminal := gterm. So mask/add/mul stay guarded as for
  SM. The chain then mirrors NPH_R22JoinSM7: `slotM_guardedT`, `op9gT`, `tx1_guardedMT`, `GT`,
  `GT_agree` (digest from NPH_R22JoinSM6.digest_of_binding) and `stage1_guardedT`.
- **`stage1_guardedT` has no premise.** For every host context and input, stage1_owned (GT c) =
  stage1_owned (S c). So every execution of the deployed 345 entry runs the FIq terminal only on
  its input domain, where it is ok.

The op9 → finish → terminal call chain is the one recorded for SM in 18a, since the terminal is a
slot of the same finish record. It rests on the same textual screen, which is flagged.

### 19c. Site coverage of the 238 FIq sites (NPH_fiq_refs_host.py, NPH_FIQ_REFS.json; NPH_R22FIqSites, L081)

The forward scan of 18c stays unused. The new screen walks **backward**. From each site it walks
upward through the definitions that reference it, and it never passes the two composed terminal
nodes (terminal_qm31 and FIq_Terminal.terminal). A definition with no definition referrer is a
top. Each top is classified:
- a deployed root: a definition of AdapterRwModel or a configuration or program record;
- referenced from theorems only;
- a tie candidate: a theorem that references it also names a deployed record (tie words widened
  to NNH_/NOC_/NHW_/NNG_/LIB_/Stage1/Run5/Run6/Host/Tx1/Tx2/adapter), so that theorem might make it
  executed.

The screen resolves names over all 13,681 replayed modules, with namespaces and opens. **Positive
controls:** NBO_FieldSemantics add/product/power, NBF_BasisInstall.install, NJJ_QueryOps.concrete,
FIp_SemanticArithmetic.mask, NFS_QueryOps.installed and the R72 circle sampler are all known to
execute. The forward scan missed NBO and NBF. Every control is classified as executing (a root
reached or a tie candidate), and none as proof-only. The screen is textual and flagged for lead
review.

| Screen class | Sites | NPH_SITES.json status |
|---|---:|---|
| COVERED_BY_TERMINAL (all in-family extracted) | 120 | TERMINAL_TOTAL |
| STOP_NODE (terminal_qm31, FIq_Terminal.terminal) | 2 | TERMINAL_TOTAL |
| PROOF_ONLY (78 outside models, 36 aliases) | 114 | NOT_EXECUTING (flagged) |
| TIE_CANDIDATE (LIB_VTerminal.native, NNG_ModelTerminal.native) | 2 | W_LEMMA |

NPH_R22FIqSites (L081, first attempt, 3.06 s, 6,669,884 KiB, 3 axiom lines, standard):
- `lib_native_ok`: LIB_VTerminal.native is ok under LIB_VTerminal.Domain. The library carriers are
  canonical by type.
- `lib_model_site`: LIB_VTerminal.model, the only definition referrer of native, runs it only under
  Domain and fails before it otherwise.
- `nng_native_ok`: at the lowered LIB arguments, NNG_ModelTerminal.native is LIB_VTerminal.native
  (NNG_LIBTerminal.native), so it is ok under Domain.

Flagged: the NNG 136 model callers of NNG_ModelTerminal.call (the c7 slot of
NNG_ConcreteCalls136.calls) are model-layer records. They are tied to the headline only by
theorems (NNH_Run6Installed.implementation and similar), and their arguments are not composed
here.

### 19d. Moved to PRECONDITION_B (tag fiq_terminal)

The same screen run on every open FIq cone definition puts all 33 of them in COVERED_BY_TERMINAL:
- the four kernels: FIq_Native.field M31.add, M31.sub, CM31.mul and CM31.square;
- 29 definitions that were OPEN: CALLER_DOMAIN_NOT_COMPOSED: the Poseidon linear layers and
  constant interpolation, the qm31_m31_dot and sum3 loops, qm31_pack_base4, the digest-binding,
  value-lane, path, preweighted and public-digest lane loops, semantic_packed, selected_claim,
  bounded_append_carry_loop, validate_transition_loop, composition_parts, and the copy-terminal
  selectors, link_weight and mask sum.

Each of them executes only inside the terminal, and the terminal is ok at every deployed
execution. So every checked operation in them returns ok on every reached input. The precedent
is SC's semantic_value_loop.body (17b). Previous judgments are kept under
`nph_judgment_before_fiq_terminal`. NPH_move_family.py gained an `NPH_ALLOW_OPEN` switch for the
29 OPEN definitions. NPH_recount.py reproduced 67/27/6/20/100 and 309 before the change.

| Judgment | Definitions |
|---|---:|
| TOTAL (a) | 67 |
| DIRECT (c) | 27 |
| domain lemma proved, caller join open | 2 (was 6) |
| precondition proved from the callers (b) | 53 (was 20) |
| open | 71 (was 100) |
| NOT_EXECUTED (excluded) | 5 |

**Rows exposed: 259 of 396** (was 309). 137 rows are served only by TOTAL, DIRECT or (b)
definitions.

Families at (b): CW, SC, R72, SM, QA and FIq. The two remaining domain-only definitions are the
canonical.Q.raw copies (item 2 below).

No executing site was found that passes a value whose bound no producer gives. No reachable input
on which the wrapping binary accepts and the checked model rejects was found. 4 scopes used so far
(L078–L081), 36 of this run's 40 remain.

Target not yet established.

### 19e. The two canonical.Q.raw copies (item 2): producers located, one context composed, Q.raw stays domain-only

One scope was used: L082 accepted NPH_R22QRawPush on the first attempt (2.30 s, 5,373,304 KiB,
swap 0, 3 axiom lines, standard, no sorry). The task now stands at 5 of the run's 40 scopes.

**Where the copies execute** (backward screen NPH_QRAW_REFS.json, the same script with the Q.raw
names as controls; textual):
- FIo copy: FIo_Native.fast_pairing.canonical.Q.raw (the NativeExternal wrapper of FIo_QRaw) is
  called only by canonical.Dot.push. Dot.push is called only by EbyKDot.push, apart from the model
  NGM_DotInduction.walk.
- EbyKDot.push has two kinds of deployed caller:
  - FIp_NativeDots.fast_dots.four_dots_one. Its three tail pushes push g[28], g[26] and g[27], with
    scalars decoded from the proof bytes. This is the op20 dots.
  - The FIo_Native.weights high_dot_loop, partial_dot_loop and push_byte_products_loop bodies.
    They push weights.field = WideExact.from_le_bytes … unwrap. These bodies are NOT_R22 wrapping
    gate bodies, but the Q.raw they reach is a checked/mixed cone definition.
- Unified copy: AspisR1CanonicalQRawUnified.canonical.Q.raw is reached through raw_entry and
  AspisR1QRawGeneratedPushConnectionV2.sourceRawFn. That is the rawFn of the claim-dot concreteOps
  pushDot (pushWithDotBackend → checked-Q push → dotViaRaw), the record of NPH_R22JoinCW4.

So the dots output producer FIp_DotsOutputCanonical.all (outside L187, section 11) is not the
producer the caller join needs. Q.raw receives the **pushed value** and the **scalar**, not the dots
output.

**Proved (NPH_R22QRawPush):**
- `checked_none`: checked_q rejects a scalar with a limb ≥ P before any Dot.push.
- `push_total`: EbyKDot.push self v x is ok for **every** state and scalar whenever the pushed value
  v is canonical.
  - At the term limit, it returns Err before any push.
  - On a non-canonical scalar, checked_q rejects first.
  - Otherwise both Dot.push calls, and so both Q.raw calls, run on canonical limbs
    (NFE_NFC_CalleeDomains.total, in the closure).
  - So the scalar side of every Q.raw call needs no caller producer.
- `g_push_site`: on NEV_DotInputs.Canonical g, every four_dots_one push is ok.

**What is missing before either copy can move to (b):**
1. Canonical g at every executed op20 dots call. The producer is located: g is a field of
   NFS_PacketRoot.Domain on the 094 path, and of NFS_QueryInvariant.Domain at every reached tx2
   query state (NPH_R22JoinCW2.reach_domain). The tie from the installed op20 slot through
   FIp_DotsAdapter.dots and four_dots to four_dots_one at the same g is not composed.
2. A canonical pushed value in the three FIo weights loop bodies. The located producer is
   WideExact.from_le_bytes success (NFS_ReadCanonical); it is not composed through those loops.
3. A canonical pushed value at the claim-dot pushDot calls of the Unified copy, inside
   owned_claim_loops on concreteOps. NPH_R22JoinCW4.owned_loop_canon keeps the parts canonical, but
   the pushed values are not yet tied to it or to the ClaimParser field reads.

No value without a producer was found. Each pushed value has a located producer, and only the ties
are missing. The two Q.raw copies stay DOMAIN_LEMMA_PROVED. Their cone entries carry
`caller_join_progress_20261110_fiq` with the path and the three missing ties.

### 19f. Item 3 (the rest of the 345 body walk)

Item 3 asked for the 345 walk for kernels that 094 does not reach. With FIq at (b), every field
family's domain-only kernels are at (b) (CW, SC, R72, SM, QA, FIq). Their contexts on the 345 entry
are composed by NPH_R22JoinSM7.stage1_guarded and NPH_R22JoinFIq.stage1_guardedT. The only
domain-only definitions left are the two Q.raw copies, which run on the tx2 and claim-dot paths
(19e), not inside the 345 body. So no kernel is waiting on more of the 345 walk. The 71 OPEN
definitions are a separate obligation: non-field loop and decoder bodies such as the samplers'
digit/div loops, TerminalDecoder encode loops, the DecodeK and record parsers, the FIp_NativeDots
loops and the accumulator and push-residue loops. They are not kernel call-site joins.

**Counts (220 executed checked or mixed definitions): 67/27/2/53/71**, as in 19d. Rows exposed:
259 of 396.

No reachable input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

## 20. Q.raw TOTAL; item 2 (loop and decoder bodies) by pattern; final counts (continuation worker, 2026-11-10, after L082)

Four scopes were used (L083–L086 of this run's 40), all capped as in section 19; L084 failed on two proof-script details (an abbrev-level rewrite and two unassigned existential witnesses) and was changed before L085. Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound]; no sorry; swap 0; peak RSS 5,398,568 KiB. The lead decision holds: no ops interface, merged module, closed-row statement or field premise is changed. The full account, the open list with pattern classes and rows, the proposed claim wording and the single list of textual-screen reliances are in **NPH_R22_FINAL_COUNTS.md**.

**Item 1 (Q.raw) — route changed, target unchanged.** Section 19e planned three caller ties to move the two canonical.Q.raw copies to (b). They are not needed: NPH_R22QRawTotal (L083) proves both copies **TOTAL for every input**. The body's checked operations are products of u32 limbs widened to u64, each at most (2^32−1)^2 < 2^64, plus PP, 2u, 2v, 2·PP, 3·P and a shift by 31; every sum is an explicit wrapping_*. The proof is the closure proof qraw_total_of_canonical_limbs with the limb premise replaced by the u32 type bound. Counts then 69/27/0/53/71 of 220; rows exposed 255 of 396.

**Item 2.** NPH_R22Loops4 (L085) and NPH_R22Loops5 (L086) close 19 bodies by pattern: TerminalDecoder encode_digest_canonical_loop.body to (b) on the reached cursor domain; EbyKFinish reduce and the two executing row_shape copies TOTAL; constant arithmetic, shift by a constant, guarded decrement/increment, cursor-then-range-read (T2Nat_RawBounds.range_success/no_wrap), point-read chains and e_byte index arithmetic DIRECT. The backward referrer screen of section 19c, generalised to arbitrary targets (NPH_refs4_host.py, output NPH_REFS4_A.json, positive controls all executing), finds 23 of the 71 bodies with no executing root; they are NOT_EXECUTED under lead ruling 1, flagged. The halfway point (36 open, rows exposed 160 of 393) was committed as d9109575dba. The remaining 29 carry `nph_pattern_class` and `nph_open_next_step` in NPH_R22_CONE.json.

**Counts (225 checked or mixed): 72 TOTAL, 42 DIRECT, 54 (b), 0 domain-only, 29 open, 28 NOT_EXECUTED; executed obligation 197. Rows exposed: 153 of 393.** 74 of them depend on exactly the nine dots/accumulate/residue bodies.

No reachable input on which the wrapping binary accepts and the checked model rejects was found. NDH absorb_ref's `160 + row` would overflow for row ≥ 96, but the body is not executed by the deployed program (proof-only reference), so no such input follows.

Target not yet established.

## 21. Item 1: the dots, accumulate and residue bodies reach (b) (continuation worker, 2026-11-10, after L086)

Five scopes were used: L087–L091 of this run's 40, all capped as in section 19. Three failed on proof-script details, and each was changed before the next scope:
- L087 and L088: the existential witness of tail_total was left unassigned. The fix gives the explicit returned pair.
- L090: pair projections were not reduced before omega, and `value 0` was not unfolded to `cursor 0`. The fix adds dsimp only and an explicit show.

Swap was 0 throughout, and peak RSS was 5,979,468 KiB. Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound], with no sorry. The lead decision holds: no ops interface, merged module, closed-row statement or field premise is changed.

**21a. Accumulator/cadence family (NPH_R22Accum, L089).** Six bodies move to (b):
- NEV_AccumulateRaw.accumulate_batched_with_node and its loop0.body, loop0_loop0.body and loop1.body;
- NEI_PushRaw.update_residue_row_loop0.body and loop1.body.

The invariant asked for is already a def predicate in the closure: S7JoinRowsTrace.Progress t 0 (toBW b), the per-row phase of term count t for all 64 residue rows.
- **Preserved.** Each push and the flush on terms % 4 = 3 preserve it (NBF_Progress.body inside NBF_RowsTotal). A push leaves the term count unchanged. accumulate_batched_with_node adds one to it once per call, after all 64 rows have been visited once.
- **Established.** The producers establish it: the pending constructor gives Progress 0 0 (NBF_FirstRows.constructor_progress), and NFS_QueryInvariant.Domain carries it at every reached query state.

New Lean statements:
- `rows_total`: the checked basis producer and the 64-row weights loop are ok, with the term count unchanged. This covers loop0 with its inner loop, and loop1 with BatchedWeights.push → update_residue_row → both residue loops.
- `tail_total`: the checked terms + 1, a.next + 1 and the field callees are ok.
- `acc_total`: the whole call is ok for every node on NFS_NEV_AccumPacket.Domain.
- `acc_site` and `installed_ok`: the caller join. At every state of NFS_QueryInvariant.Domain inside the loop guard, with the canonical line value, the installed accumulate equals NFS_AccumInstall.run and is ok.

The enclosing call is ok, so every execution of the five inner bodies inside it is ok.

The earlier OPEN notes asked for "terms < MAX and a.next < finish" and "n ≤ 128". Both are subsumed:
- the counters are < 22 by the query invariant;
- the basis width is the literal 64, because rows_cut rewrites len a.weights to 64.

**21b. Dots family (NPH_R22Dots, L091).** Three bodies move to (b): four_dots_one, four_dots_one_loop0.body and four_dots_one_loop0_loop0.body. Two new def predicates are introduced:
- `InnerInv`: at most 4 terms per window, ending at or before 26, with sums ≤ (terms so far)·(P−1)².
- `OuterInv`: after k ≤ 7 windows the StepBy iterator is at min(4k, 26), with limbs ≤ k·R.

Each is entered by its caller and kept by every successful step:
- inner_entry and inner_step;
- outer_entry and outer_step.

On them:
- every checked operation is ok: slot_ops, read_arith, update_ok, outer_ops;
- the inner body is ok whenever the current term's scalar read succeeds (inner_ok).

read_arith proves that the read's only checked operations are the cursor arithmetic. The rest is the range index, try_from, unwraps and the M31 decode. These aborts happen in both profiles; this reading is textual and listed in FINAL_COUNTS section 4.

The caller domain is slot < 4 and canonical g:
- the slots are the literals of four_dots (adapter_calls);
- on tx1, g comes from NFS_PacketRoot.Domain.gCanonical (tx1_g);
- on tx2, g comes from NFW_PowersDomain.query_domain.

**21c. Caller structure.** A new read-only backward screen, NPH_REFS5.json (NPH_refs4_host.py on NPH_REFS5_SPEC.json, MemoryHigh 3G / MemoryMax 4G), classifies all 12 targets COVERED_BY_TERMINAL:
- every upward path meets NEV accumulate or NFS_AccumInstall.run (accumulate family);
- every upward path meets FIp_DotsAdapter.dots (dots family);
- the other tops are theorem-only.

This screen is textual and flagged.

**Counts (225 checked or mixed): 72 TOTAL, 42 DIRECT, 63 (b), 0 domain-only, 20 open, 28 NOT_EXECUTED; executed obligation 197.** Rows exposed: **73 of 393** (153 before). Of the exposed rows, 80 had no open dependency outside these nine, and 74 depended on exactly these nine.

Next, item 2: the 7 caller-owed cursor bounds and the 2 caller-domain index bodies. Item 1 closed four_dots_one, so 1 index body is left (weights.field).

No reachable input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.

### 21d. Items 2 and 3 (same run, after commit b3fd3b3fbd7)

Five more scopes were used: L092–L096, which makes 10 of the run's 40. Two failed on proof-script details and were changed before the next scope:
- L092: a conjunct shape in frontier_ops/cc_ops.
- L094: the bound proofs of widen_val and add_small_ops.

Swap was 0 throughout, and every accepted `#print axioms` line is standard. One more read-only screen was run: NPH_REFS6.json, the direct referrers of the item-2 targets.

**Item 2: NPH_R22Cursor (L093).** Six definitions moved.
- **bytes32_loop.body and digest_loop.body → (b).** The cursor bound comes from the bodies' own point-read chains (BInv/DInv, word32_bound), so no caller length is needed.
- **decode_frontier_loop.body → DIRECT.** Its guard is level < 20.
- **expand_semantic_loop.body → DIRECT.** Each cursor add is followed by a range access: cursor_direct for reads, and the new mut_cursor_direct / range_mut_success for index_mut.
- **decode_k_value → (b) on DK.** decode_k's own checked_mul and checked_add guards establish the domain (dk_guards, using the converses checked_mul_some and checked_add_some). The loop keeps end = N (dk_value, dk_step).
- **copy_chunk_loop.body → (b).** The bound chunk·32 + 31 ≤ max comes from values_owned_reference's checked 2·len and count = len/16 (vo_guards, cc_domain).

Two item-2 definitions stay open, with their producers located (FINAL_COUNTS section 3):
- **weights.field.** The closure's NJU_FieldScalar.checked covers i < 64. The finish dot's j < len weights and the polynomial/claim-parser indices still need composing at the deployed finish.
- **values_owned_reference.** Its 2·len needs len ≤ 1856, which comes from the compact row size through expandValues.

**Item 3: NPH_R22Direct (L095) and NPH_R22Gamma (L096).**

Moved to DIRECT:
- parse_record and parse_record_at. Every row_shape size is ≤ 3712. For parse_record_at, get_cursor_direct covers offset + length; the Err/abort reading is flagged.
- body_byte: a guarded subtraction chain with constant divisors.
- qm31_div_pass_loop.body, low_base_p_digits_loop0.body and add_small_base_p_loop.body. Every checked operation is ok for every input under the guard, so the remainder and digit invariants named earlier are not needed.
- write_parent and leaf_step: the increment follows a successful Array.update on a 16-entry array.

Moved to (b): gamma_sample. The quotient is ≤ 256 on low_base_p_digits, and both closure helper records install it (flagged caller reading).

Still open:
- **binary_step.** I found a concrete reason it is not DIRECT. len(nodes) − s.at has no guard, and a wrapped difference below 32 takes the Stop branch, an accepting path, where the checked model aborts. That needs s.at > len(nodes) − 32 + 2^64, which no reached state is known to reach. The traversal invariant s.at ≤ len(nodes) closes it.
- **prepare.** It needs the installed op15 constant.

**Item 4.** r24_canonical_mul stays as recorded: a source-refinement obligation with no frozen counterpart.

**Counts (225 checked or mixed): 72 TOTAL, 52 DIRECT, 68 (b), 0 domain-only, 5 open, 28 NOT_EXECUTED; executed obligation 197. Rows exposed: 55 of 393** (153 at the start of this run, 73 after item 1).

New textual reliances, all listed in FINAL_COUNTS section 4:
- NPH_REFS5.json and NPH_REFS6.json;
- the parse_record_at Err/abort reading;
- the gamma helper-record reading;
- the read-failure reading of the dots inner body, under the checked-operation enumeration row.

No reachable input on which the wrapping binary accepts and the checked model rejects was found. binary_step's unguarded subtraction is the one place where such an input would need a reached state with s.at > len(nodes); none is known.

Next concrete deliverables:
1. binary_step: the s.at ≤ len(nodes) traversal invariant over level_rows.
2. weights.field: compose the finish dot's weights length ≤ 64 and the polynomial/claim indices on the tx2 finish context (NPH_R22JoinCW2).
3. values_owned_reference: the range-index length lemma plus the expandValues tie.
4. prepare: the op15 value.
5. r24_canonical_mul: provenance first.

Target not yet established.

## 22. Items 1–4 of the 2026-11-10 continuation (worker after commit 56b95b5c29e)

Seven scopes were used, L097–L103 of this run's 30, one at a time. Each ran under the same caps as section 21. From L098 on, every launch also checked `free -g` available ≥ 12 GB, per the lead's instruction while Stream B runs extraction lanes. Three scopes failed on proof-script details, all on NPH_R22ValuesSite, and each was changed before the next scope (L099, L100, L101; see NPH_COMPILE.tsv). Swap was 0 throughout and peak RSS was 6,809,376 KiB. Every accepted `#print axioms` line is within [propext, Classical.choice, Quot.sound], with no sorry. One read-only screen was run, NPH_REFS7.json. The lead decision holds: no ops interface, merged module, closed-row statement or field premise is changed.

**22a. binary_step → (b) (NPH_R22Binary, L097).** The traversal invariant is the def predicate AtInv nodes s := s.at ≤ len nodes, over the set Reached of traversal states.
- **Entry.** Reached starts at {s with at := 0}, the levels entry used by verify_owned and by Port9OR_P6Verify.factored.
- **Closure.** Reached is closed under a Next step of binary_step (step_next) and a Done result of level_rows (rows_done).
- **Result.** reached_inv shows AtInv holds on every reached state. reached_ops shows every checked operation of binary_step is ok there with its mathematical value. So len(nodes) − s.at never wraps on a reached state, and the Stop test decides identically in both profiles.

No hash totality or node-length premise is used. No reached state with s.at > len(nodes) exists, so there is no wrapping-accepts/checked-rejects input at this site.

The earlier note was wrong to call the Stop branch accepting: Stop makes verify_owned return false. The call structure (only level_rows → levels → verify_owned/factored → Port4B_VerifyInstall.verify) is read from NPH_REFS7.json and the gate text, and is flagged.

**22b. values_owned_reference → (b) (NPH_R22Values L098, NPH_R22ValuesSite L102).** The checked 2·len is ok for len ≤ 1856.
- **Compact expand site.** The argument is input[i1, i1 + size/2), and size ≤ 3712 comes from the compact row_shape table (compact_site).
- **Prepare op11 site.** At every installed configuration op11 is expandValues. The argument is proof[7031, 7495) of width 464: op12 = 16, op13 = 7015, op14 = 464, all by rfl for every cfg (installed_y1_site).
- **Flagged.** The call-site bindings, and the coverage of NDO_JFw_Row.runRow, are textual.

**22c. prepare → (b) (NPH_R22Values, L098).** op15 of currentInstalled cfg is 13831 for every cfg, by rfl, and the op8 replacement leaves it unchanged. LOGICAL_Y1 = 928, so the add gives 14759 and is ok. The executed-record reading is flagged.

**22d. weights.field: OPEN → domain lemma proved, caller join open (NPH_R22FieldSites, L103).** The domain i < 64 is now stated at every located site:
- the literals 0..6 (finish round, polynomial, FIn_ExtractFuns);
- the finish dot, under len weights ≤ 64;
- the claim dot, under l < 64.

Two producers remain uncomposed:
- **Finish weights length.** At the deployed tx2 finish the weights are {a1 with weights := deref_mut_back (op9 pending (deref_mut a1.weights))}. Composing their length needs two links: op6 returns a reached NPH_R22JoinCW2.Reach state, which carries NFS_QueryInvariant.Domain.width = 64, and the Port3_FlushInstall.flush length preservation. FIn_WeightLength.twelve gives 64 only on an accepted-run witness.
- **Claim-dot iterator bound** l < 64.

This is not fail/fail, because a wrapped window can be valid (i = 2^59 gives [0, 32)).

**22e. r24_canonical_mul** is unchanged: a source-refinement obligation with no frozen counterpart.

**Counts (225 checked or mixed): 72 TOTAL, 52 DIRECT, 71 (b), 1 domain-only, 1 open, 28 NOT_EXECUTED; executed obligation 197. Rows exposed: 44 of 393** (55 at the start of this run). Of these, 17 rows have weights.field as their only blocker and 7 have r24_canonical_mul.

Proposed final row wording: FINAL_COUNTS section 5.

Next concrete deliverables:
1. weights.field producer (1): a Lean statement that the tx2 op6 result is a Reach state of NPH_R22JoinCW2, plus flush length preservation, composed to dot_site.
2. weights.field producer (2): the claim-dot loop entry's iterator range bound, composed to claim_site.
3. r24_canonical_mul: provenance first.

No reachable input on which the wrapping binary accepts and the checked model rejects was found.

Target not yet established.
