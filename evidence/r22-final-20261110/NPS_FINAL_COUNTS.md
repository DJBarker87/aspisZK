# NPS_ R22 final counts (CheckedVsWrapping), 2026-11-10, local continuation of NPR_

Job NPS_, branch codex/cx-r22l-20261110, run locally on the Mac (no build host). This file updates NPR_FINAL_COUNTS.md for one change: `AspisR72Sampler.field.r24_canonical_mul` moves from OPEN to TOTAL (a). NPR_ and NPH_ files are unchanged. Frozen target 4bb3b3f. Machine record: NPS_R22_CONE.json, generated from NPR_R22_CONE.json by NPS_cone_update.py and recounted by the unchanged NPH_recount.py. **Target not yet established.**

## 1. Counts

| Judgment | Definitions | Start of this run (NPR_) | Change |
|---|---:|---:|---:|
| TOTAL (a) | 73 | 72 | +1 |
| DIRECT (c) | 52 | 52 | 0 |
| precondition proved from the callers (b) | 72 | 72 | 0 |
| domain lemma proved, caller join open | 0 | 0 | 0 |
| open | 0 | 1 | -1 |
| NOT_EXECUTED (excluded, ruling 1) | 28 | 28 | 0 |
| **executed (the obligation)** | **197** | 197 | 0 |
| all checked or mixed | 225 | 225 | 0 |

By body class: CHECKED/TOTAL 67, CHECKED/DIRECT 50, CHECKED/(b) 72, CHECKED/NOT_EXECUTED 28, MIXED/TOTAL 6, MIXED/DIRECT 2.

Rows. The executed checked or mixed definitions touch **393** CLOSED rows. **0** of them depend on an open or domain-only definition (27 at the start of this run). All 393 are served only by TOTAL, DIRECT or (b) definitions. The 27 rows removed are the rows listed in NPR_FINAL_COUNTS.md section 6, for which r24_canonical_mul was the only blocker.

How the counts were obtained. `python3 -I NPS_cone_update.py` changes the one entry and recounts. `python3 -I NPH_recount.py NPS_R22_CONE.json` recounts with NPH_'s script and gives the same result: TOTAL_PROVED 73, DIRECT 52, PRECONDITION_B 72, NOT_EXECUTED 28, no OPEN, touched 393, exposed 0, served 393. The same script on NPR_R22_CONE.json reproduces NPR_'s 72/52/72/1 and 27 of 393. The counting rule is the one NPR_ and NPH_ used: judgment = first word of nph_judgment, only CHECKED and MIXED bodies, NOT_EXECUTED excluded from rows, and a row counts as exposed when any definition touching it is OPEN or DOMAIN_LEMMA_PROVED. (The cone JSON's `denominator: 220` field is inherited from an earlier NPH_ state and is not used by either script.)

`field.r24_canonical_mul.PP` is not a separate entry in the cone (the census has two r24 entries: the main body and the closure call). Its totality is proved anyway (`PP_total`). The closure call was already TOTAL (NPH_R22CM31.R72_r24_closure_total).

## 2. What was proved

Module NPS_src/NPS_R24Total.lean (namespace AspisR1.NPS_R24Total), imports NPH_R22CM31 only.

Main theorem, in the statement form of NPH_R22QRawTotal.unified_total:

```lean
theorem r24_canonical_mul_total (left right : AspisR72Sampler.field.QM31) :
    ∃ out : Option AspisR72Sampler.field.QM31,
      AspisR72Sampler.field.r24_canonical_mul left right = .ok out
```

No hypothesis on the inputs. The eight guards `x ≥ field.P` return `ok none`. That is an ordinary success, not a failure. In the remaining branch, each checked site has its own lemma:

| Site | Count | Lemma | Bound used |
|---|---:|---|---|
| `cast x * cast y`, u32 limbs widened to u64 | 16 | `limb_mul_ok` | each factor < 2^32, so the product ≤ (2^32-1)^2 < 2^64. Holds for every u32, so the `< P` guards are not needed |
| `PP = cast P * cast P` | 1 | `PP_ok`, `PP_total` | value P^2 < 2^62 |
| closure call (mask, checked `>>> 31#i32`, wrapping add) | 2 | `closure_ok` | ok for every u64 argument. Output ≤ P + (2^64-1)/2^31 < 2^34 |
| `2 * u`, `2 * v`, `2 * PP` | 3 | `two_mul_ok` | the operand is < 2^63 (u, v < 2^34; PP < 2^62) |
| `3 * from P` | 1 | `three_P_ok` | 3P < 2^64 |
| `M31.reduce_u64` | 4 | `reduce_ok` | TOTAL on every u64 (NPH_R22CM31.R72_reduce_wrapper, NPH_R22FieldRef.refReduce_total) |
| `CM31.new` | 2 | `new_ok` | `ok` by definition |

Every addition and subtraction in the body is an explicit `core.num.U64.wrapping_add`/`wrapping_sub`, and the casts and `FromU64U32.from` are `lift`ed pure functions, so neither can fail. The body is put in sequence with the generic lemma `step` (a successful bind followed by a successful continuation succeeds). The guards are split by `by_cases` and `if_pos`/`if_neg`. No broad simp, decide or norm_num touches the body. The only `norm_num` calls evaluate the literals `2#u64` and `3#u64`. Before writing the proof, the body was printed from the L187 closure olean (NPS_C001). It matches the research-branch source selected-canonical-R72-Funs-20261019/source.lean, lines 412-485.

No checked operation in the body can fail on any input. None needed to be reported.

What this establishes: checked totality of the gate body. As for the closure call and the other TOTAL entries of the mixed class, the transfer from checked to wrapping (R22TotalCheckedComposition.extracted_total_R22) still depends on the P6/P7 operational interpretation. That interpretation is unchanged here.

## 3. Provenance remains open (separate obligation)

This result is R22 arithmetic only. `AspisR72Sampler.field.r24_canonical_mul` is still **NO_FROZEN_COUNTERPART**. It is a gate-only helper from the probe crate file `src/r24_guarded_qm.rs` and has no counterpart in the frozen 4bb3b3f source. The same holds for its closure and PP. Neither this proof nor the move in NPS_R22_CONE.json changes that status, and no source-refinement claim is made. Before any release claim can rely on the 27 rows in NPR_FINAL_COUNTS.md section 6, the provenance obligation must be closed: show that the deployed QM31 multiplication refines this body, or replace the body by a frozen counterpart and re-judge that one. Provenance belongs to Stream C (P6).

## 4. Textual reliances

These are unchanged from NPR_FINAL_COUNTS.md section 4 (R-1 to R-7). R-6 (completeness of each body's checked-operation list) also covers this body. The site table in section 2 was read from the printed olean term, not produced by an elaboration-time scan.

## 5. Validation

The Lean work used four local compiles, one Lean process at a time. Each used toolchain leanprover/lean4 v4.32.0, `lean -M7000 -DElab.async=false` and a 180 s alarm. LEAN_PATH was objs : base : overlay-NPH : overlay-NPR : overlay-NPS, and the wrapper is NPS_compile.sh, a copy of NPR_compile.sh with paths changed.

| id | target | exit | wall (s) | peak RSS (bytes) | note |
|---|---|---:|---:|---:|---|
| NPS_C001 | NPS_Probe | 1 | 45.62 | 4,030,693,376 | probe; prints succeeded. One `#check` named a non-existent constant |
| NPS_C002 | NPS_R24Total | 1 | 56.93 | 4,221,452,288 | `split_ifs` hit the simp step limit |
| NPS_C003 | NPS_R24Total | 0 | 22.66 | 4,296,671,232 | accepted |
| NPS_C004 | NPS_Audit | 0 | 8.93 | 4,291,018,752 | 11 `#print axioms` lines |

The longest wall time was 56.93 s and peak RSS was 4,296,671,232 bytes (4.00 GiB). This Mac has no cgroup, so the only memory cap was Lean's -M7000. Host swap in use was 6.9-7.0 GB throughout. It is recorded, not zero.

Axioms (NPS_C004): step and new_ok depend on no axioms. P_val, limb_mul_ok, PP_ok, PP_total, closure_ok, two_mul_ok, three_P_ok, reduce_ok and r24_canonical_mul_total each depend on [propext, Classical.choice, Quot.sound]. There is no sorry, no axiom, no native_decide and no raised limit. Object hashes are in NPS_OVERLAY_NPS.sha256. Every row is in NPS_COMPILE.tsv, with logs in NPS_logs/. Source revision: 7b8114b7a27 plus this commit.

These are focused compiles against cached closure objects. They are not a coherent rebuild of the release closure. There was no host job, extraction, manifest replay, push or deletion.

## 6. Proposed wording change for the claim document (section 4.3, CheckedVsWrapping row)

Replace the status and residual paragraphs of NPR_FINAL_COUNTS.md section 5 with:

> Status at 4bb3b3f (NPH_, NPR_, NPS_, evidence/r22-final-20261110/NPS_FINAL_COUNTS.md): there are 225 checked or mixed definitions. 28 are proof-only references, excluded under lead ruling 1. Of the 197 executed, 73 are TOTAL, 52 DIRECT and 72 (b). None is open. None of the 393 CLOSED rows these definitions serve depends on an open definition. One TOTAL definition, AspisR72Sampler.field.r24_canonical_mul (NPS_R24Total.r24_canonical_mul_total), has no frozen counterpart. Its source refinement is a separate provenance obligation, and the 27 rows it serves inherit that obligation.

The removal condition is unchanged: each textual reliance R-1 to R-7 must be replaced or accepted by name, and the final replayed closure must be coherent. The row stays OPEN until then.

Next concrete deliverables: (1) r24_canonical_mul provenance (Stream C); (2) Lean-side referrer and checked-operation scans for R-3, R-4 and R-6; (3) the R-5 stepping proof; (4) the coherent replay of the final dependency closure with the NPH_, NPR_ and NPS_ modules on a build host.

Target not yet established.
