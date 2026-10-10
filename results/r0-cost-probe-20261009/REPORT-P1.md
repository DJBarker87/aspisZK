# P1′ COST PROBE — B measured; stopped at reconciliation

**Unproved COST PROBE. B’s internal marker partition is exact, but its costs do not reconcile to S4 using the calibrated logging cost. The required stop rule is triggered. C0′ and C2–C5 have not started. C1 was not measured.**

Base: `origin/v8-reference` at `bedd0420705bb13e3b1c5a45f308762a736aa260`. Branch: `codex/r0-cost-probe-p1-20261009`. The superseding P1′ order and R0 §8 were read. The earlier P1 work and its preflight are retained on `codex/r0-cost-probe-p1-pre-prime-20261010`; the active worktree is `.worktrees/r0-cost-probe-p1-prime`. Historical P1 C0/C1 figures are excluded.

C0 is the existing R-E4 S4 measurement, **15,078,299 / 15,070,869 CU**, imported with source hashes in [c0-inherited.json](c0-inherited.json). It was not executed again. No reference prover, `r0/onchain.rs`, fixture source, or Lean file changed. B uses the default-off `r0-cost-probe` feature and separate core, statement, prover, program and driver modules.

## B gate results

- The separate probe prover generated both 95,712-byte proofs. Both proofs and public-input byte strings match S4 bitwise. Native acceptance passes.
- All **1,894** recorded rejection results match S4, and both native tests pass. Closeout review found a coverage gap: **1,880** end-to-end cases exercise the probe-versus-S4 differential; the other **14 fixed-challenge V1/V2 cases still invoke reference helpers**. Thus the full probe corpus gate is **incomplete**, despite the preserved count and matching records. Exact errors, phase order, challenge/query bytes and passive field-byte traces are compared for both honest fixtures and the 1,880 end-to-end rejections. See [coverage review](b-coverage-review.json), [equality](b-equality.json), [native log](b-native.log), and [rejection records](fixtures/b-corruption-cases.json).
- `r0-op-count`: every inclusive and exclusive count in every phase equals the recorded S4 counts, for both fixtures. This is a native operation comparison, not a C0 CU rerun.
- SBF audit: **zero reachable stack diagnostics**. The conservative call-graph closure contains all 265 linked functions; all 38 diagnosed functions (63 diagnostic lines) are absent from the linked ELF. The unstripped and measured `.text` hashes match. See the single [stack-audit JSON](b-stack-isolated/stack-audit.json).
- Heap high-water: **131,032 bytes** for both completed DIAGNOSTIC runs, below 256 KiB.
- Acceptance at 1,400,000: **0/5 completed for each fixture**; all five results are identical per fixture. Both abort inside Semantic, after the `parsed` coarse marker, at 1,399,644 verifier CU (1,400,000 harness CU). The last fine marker is `b:-sem.transcript_hash`; the following sampler does not complete.
- DIAGNOSTIC at 200M: both runs complete. **15,197,496 / 15,190,066 verifier CU** (15,197,852 / 15,190,422 harness CU). These are the instrumented B costs.
- No optimization was made. [The source-copy audit](b-source-copy-audit.json) finds the same onchain Rust tokens after removing B markers and the diagnostic argument, and unchanged protected reference sources.

## Reconciliation — STOP

Consecutive identical marker calls cost **206 CU** on both fixtures. Nested intervals plus explicit unmarked intervals sum exactly to every B coarse phase. The comparison against recorded S4 is below; all deltas and residuals are identical for transfer and withdrawal. A positive/negative residual is additional/unaccounted saving relative to the calibrated logger calls. It is not silently absorbed into a tolerance.

| Phase | S4 transfer CU | B transfer CU | Difference | Fine markers | Calibrated logging CU | Residual |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| semantic | 2,647,122 | 2,685,075 | 37,953 | 186 | 38,316 | -363 |
| chord-claims | 968,572 | 974,515 | 5,943 | 28 | 5,768 | 175 |
| merkle | 641,001 | 640,651 | -350 | 0 | 0 | -350 |
| v1 | 3,010,106 | 3,081,732 | 71,626 | 260 | 53,560 | 18,066 |
| v2 | 7,803,350 | 7,806,757 | 3,407 | 24 | 4,944 | -1,537 |

V1 fibre 0 changes by 55,267 CU; its 260 markers explain 53,560 CU, leaving **1,707 CU**. Each of the other 21 fibres changes by exactly **779 CU** despite emitting no fine markers. The added diagnostic guards provide a source-level explanation for extra work, but neither their exact cost nor the remaining code-generation shifts has been reconciled. Merkle has no fine markers and changes by −350 CU; V2 has a −1,537-CU residual. **The S4 reconciliation gate is not passed.** No SBF or CU rerun was launched after this reconciliation failure. The separate 14-case probe-coverage gap was found during read-only closeout and is also left open; no post-stop test run was made.

[b-breakdown.json](b-breakdown.json) retains the raw partition. [b-reconciliation.json](b-reconciliation.json) retains fixed-marker debits, every phase/count comparison, and the explicit failed gate. The following breakdown is an observation of B, not a validated reconstruction of S4.

## Semantic and M1 comparison

All B rows below are **raw exclusive intervals**, including marker costs. They partition the Semantic coarse interval. M1 is the requested historical comparison; protocol and arithmetic shapes differ.

| Semantic work | B transfer CU | B withdrawal CU | M1 CU |
| --- | ---: | ---: | ---: |
| Parse and canonical checks | 10,306 | 10,306 | — |
| Transcript / sumcheck (detail below) | 1,856,319 | 1,855,835 | 140,757 |
| Terminal including mask | 641,100 | 637,692 | 286,713 |
| Point/extra claims and their two row checks | 125,392 | 125,021 | — |
| Handoff | 49,869 | 49,854 | — |
| Unmarked phase boundaries and return | 2,089 | 2,089 | — |
| **Total** | **2,685,075** | **2,680,797** | **427,470** |

| Transcript / sumcheck detail | B transfer CU | B withdrawal CU |
| --- | ---: | ---: |
| Public encoding / transcript initialization | 7,965 | 7,833 |
| Rows 0–14 sampling and orchestration, exclusive of checks/hash | 817,145 | 816,964 |
| 25 schedule/canonical row checks | 12,058 | 12,058 |
| 27 absorb/squeeze/advance hash intervals (includes rows 25–26) | 24,400 | 24,400 |
| Ten α samplers and loop orchestration, exclusive of nested work | 552,037 | 552,094 |
| Initial claim decode | 246 | 246 |
| Ten polynomial decodes | 22,670 | 22,670 |
| Ten recurrence boundary checks | 26,270 | 26,265 |
| Ten α-round polynomial evaluations | 393,528 | 393,305 |

**Where the ≈2.2M semantic excess sits:** the two sampling/orchestration buckets occupy **1,369,182 raw CU** (transfer). Source inspection identifies `qm31_sample` as the common remaining operation: it performs a 256-bit binary long division in `reduce_rank`, followed by eight base-P divisions in `base_p_digits`. This is an attribution from measured surrounding intervals and source inspection, not an isolated measurement of the reducer. The ten E-valued α-polynomial evaluations cost another **393,528 CU**. The terminal including mask is **641,100 CU**, **354,387 CU above M1’s terminal** before correcting marker overhead. Point/extra handling and handoff add 175,261 CU. Direct hash intervals are only 24,400 CU and the initial canonical parse is only 10,306 CU. These observations identify sampler reduction, E polynomial/terminal arithmetic, and handoff as the cost locations; they do not establish an optimization saving.

The exact inherited S4 excess over M1 is 2,219,652 / 2,215,374 CU. Raw B excess is 2,257,605 / 2,253,327 CU. The 37,953-CU difference per fixture is kept in the reconciliation table, not attributed to the protocol.

## Prepare / ChordClaims

Raw exclusive intervals; the full ChordClaims phase also includes `OpeningView::parse` before `prepare` and the replayed-point check after it.

| Work | B transfer CU | B withdrawal CU |
| --- | ---: | ---: |
| unmarked | 9,755 | 9,730 |
| prepare.opening_parse | 231,439 | 231,439 |
| prepare.transcript_z0 | 62,278 | 61,908 |
| prepare.y0_decode | 1,456 | 1,456 |
| prepare.transcript_z1 | 58,081 | 58,080 |
| prepare.data_copy | 45,257 | 45,249 |
| prepare.validate_points | 5,601 | 5,617 |
| prepare.transcript_batch | 154,315 | 154,182 |
| prepare.v1_invariants | 41,818 | 41,824 |
| prepare.interpolant | 80,366 | 80,352 |
| prepare.chord_pair | 6,304 | 6,304 |
| prepare.claim_prime | 217,290 | 217,287 |
| prepare.transcript_alpha | 50,829 | 50,707 |
| prepare.query_sampling | 9,347 | 9,347 |
| prepare.handoff_check | 379 | 379 |
| **Total** | **974,515** | **973,861** |

**Where the ≈0.77M prepare excess sits:** opening parse/canonical checks cost **231,439 CU**; z0/z1/batch/α transcript-and-sampler intervals total **325,503 CU**; y0 decode plus data copy cost **46,713 CU**; remaining V1 invariant setup costs **41,818 CU**. `claim_prime` itself costs **217,290 CU**, while interpolant plus chord pair cost **86,670 CU**. Query sampling, including its final-message absorb, costs 9,347 CU. The 200,000-CU comparator was a lead arithmetic estimate, not a measured implementation: S4 minus that estimate is 768,572 / 767,918 CU. Parsing, sampler conversion, representation work, and an understated arithmetic subtotal explain the location of the discrepancy; the failed B reconciliation prevents presenting this as an exact S4 excess allocation.

## One fibre V1 and V2

V1 fibre 0 only emits fine markers. Decoding remains inside the original four dot products; markers did not hoist it. Inverse intervals include line evaluation and the following E×K numerator product, in original order. Raw dot intervals include the start markers of their nested decode intervals.

| V1 fibre 0 work | Transfer raw CU | Withdrawal raw CU | Calls |
| --- | ---: | ---: | ---: |
| unmarked | 5,811 | 5,747 | — |
| v1.dots | 56,158 | 56,190 | 4 |
| v1.value_decode | 33,084 | 33,084 | 116 |
| v1.numerator | 2,651 | 2,650 | 4 |
| v1.inversions_products | 8,086 | 8,096 | 4 |
| v1.fold | 21,669 | 21,651 | 1 |
| v1.final_encoder | 64,532 | 64,506 | 1 |
| **Total** | **191,991** | **191,924** | — |

After subtracting only assigned fixed logger costs, the transfer value-decode interval is 9,188 CU, the four dots 31,438 CU, fold 21,463 CU and final encoder 64,326 CU. These are diagnostic debits, not reconciled S4 component estimates.

| V2 work | Transfer raw CU | Withdrawal raw CU | Calls |
| --- | ---: | ---: | ---: |
| unmarked | 16,525 | 16,530 | — |
| v2.G | 1,047,619 | 1,045,582 | 1 |
| v2.workspace_line | 14,618 | 14,628 | 1 |
| v2.images | 5,771 | 5,783 | 1 |
| v2.chord_weights | 3,163,882 | 3,165,314 | 1 |
| v2.indicator_sum | 98,839 | 98,728 | 1 |
| v2.tensor | 1,090,356 | 1,090,321 | 3 |
| v2.pairing | 2,367,456 | 2,366,926 | 3 |
| v2.image_combine | 1,691 | 1,686 | 1 |
| **Total** | **7,806,757** | **7,805,498** | — |

G includes the degree-six polynomial evaluation, dF transpose and initial workspace allocation. The three tensor and three pairing intervals are individually ordered in each diagnostic log; the table sums each kind. Images are measured before the in-place chord map, as in S4.

## Cumulative cost table

**All rows are COST PROBE evidence.** C0 is inherited S4; B is instrumentation only and failed reconciliation. Multiplications below are native exclusive `r0-op-count` totals: E×E / E×K / E×F and K×K / K×F / F×F. The complete per-phase inclusive/exclusive arrays are retained in the count JSON files.

| Configuration / fixture | Semantic | Prepare | Merkle ×22 | V1 ×22 | V2 | Other | Total CU | Proof bytes | E multiplications | K / F multiplications |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| C0 (inherited S4) / transfer | 2,647,122 | 968,572 | 641,001 | 3,010,106 | 7,803,350 | 8,148 | 15,078,299 | 95,712 | 1,601 / 6,507 / 11,934 | 4,362 / 466 / 15,548 |
| C0 (inherited S4) / withdrawal | 2,642,844 | 967,918 | 641,165 | 3,008,755 | 7,802,091 | 8,096 | 15,070,869 | 95,712 | 1,601 / 6,507 / 11,934 | 4,353 / 466 / 15,428 |
| B (unreconciled) / transfer | 2,685,075 | 974,515 | 640,651 | 3,081,732 | 7,806,757 | 8,766 | 15,197,496 | 95,712 | 1,601 / 6,507 / 11,934 | 4,362 / 466 / 15,548 |
| B (unreconciled) / withdrawal | 2,680,797 | 973,861 | 640,815 | 3,080,381 | 7,805,498 | 8,714 | 15,190,066 | 95,712 | 1,601 / 6,507 / 11,934 | 4,353 / 466 / 15,428 |

No configuration in this report completes at ≤1,400,000 CU. Headroom to 1,300,000 for a qualifying configuration is **not available**. C0′, C2, C3, C4, C5(a), C5(b), C5(c): not started because B’s gate did not pass. C1: excluded from measurement. No conclusion about those unmeasured configurations is drawn.

| Phase (same counts for C0 and B) | E×E | E×K | E×F | K×K transfer / withdrawal | K×F | F×F transfer / withdrawal |
| --- | ---: | ---: | ---: | --- | ---: | --- |
| Semantic | 311 | 0 | 0 | 1,199 / 1,190 | 288 | 1,602 / 1,602 |
| ChordClaims | 260 | 9 | 0 | 94 / 94 | 0 | 0 / 0 |
| Merkle | 0 | 0 | 0 | 0 / 0 | 0 | 0 / 0 |
| V1 | 242 | 352 | 8,096 | 0 / 0 | 176 | 12,378 / 12,258 |
| V2 | 788 | 6,146 | 3,838 | 3,069 / 3,069 | 2 | 1,568 / 1,568 |

## Reproducibility, resources and retained artifacts

B source instrumentation is at `bdb9831a7`; logger calibration at `e0c11a5fa`; SBF/source evidence at `04d78bee2`; isolated-cache and measurement runner at `fac870e7d`. Every job records its full source revision, input hashes, command, exit status, wall time, sampled aggregate RSS, cgroup memory peak and swap. [Environment](b-environment.json): native Rust/Cargo 1.94.1; cargo-build-sbf 3.1.13; platform-tools 1.52 / SBF Rust 1.89.0; LiteSVM 0.16.0 / Agave 4.2.1.

Every host job used its own scope with **MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0** and reservation checks against a 50-GiB host working limit. No cap was raised. All task scopes report zero swap. Highest sampled aggregate build RSS was 1,266,892,800 bytes; highest build cgroup peak was 1,005,527,040 bytes. The cache-copy job reached 4,295,671,808 bytes of cgroup memory, largely filesystem cache; its sampled RSS was 15,699,968 bytes.

The first stack-audit attempt failed before producing a stack-audit JSON: another P1 job overwrote the shared target’s unstripped ELF with a different artifact. The original stripped B ELF was retained. The dependency cache was copied to this job’s own target directory, and a cached SBF rebuild recovered the matching unstripped artifact. The original and recovered stripped B ELF hashes are identical. This was recovery of a missing matching audit artifact; no CU measurement had run and no measurement was repeated. The failed [audit log](b-stack.log) and its [resource record](b-stack.json) remain in evidence.

Measured ELF: SHA-256 `d4d17fedf9fcde1213040f3689bcf1ed432a55091c069cda63ee41a0d41fadd5`, **721,552 bytes**. The [artifact manifest](b-artifact-manifest.json) records sizes and hashes for all retained proof/public blobs, native binaries, both ELF pairs, text dumps, symbols and disassembly. The initial `b-elf/aspis_verifier.unstripped.so` is the rejected mismatched cache artifact; only `b-elf-isolated/aspis_verifier.unstripped.so` is the audited pair.

Artifacts remain on `nuc` under `/home/dombarker/project-offloads/aspis-r0-p1-prime-20261009/results/r0-cost-probe-20261009/`. Only JSON/Markdown/log evidence is committed; no ELF, `.so`, `.text`, disassembly, proof blobs or keys are committed. Generated program and LiteSVM payer keys are retained securely; no key cleanup occurred. The report records a completed B measurement attempt and a failed reconciliation gate, not completion of P1′.
