# V403 handoff

V403 remains **OPEN**. The privacy target is **not yet established**.
Branch: `codex/pv-canon-20261027`; launch/base revision: `ea81432954`.
No shipped code, shared env-J source, existing proof module, trust structure,
or endpoint premise was changed. Endpoint premises removed/added/weakened:
**0/0/0**. T remains exactly entropy_law, entropy_kernel, observation.

## What is proved

The predicates M/C/Q mean raw representatives below P=2147483647, componentwise;
they do not quotient away noncanonical words. Coeffs means every coefficient is Q.
`PV_Canon_Limbs` proves this is precisely the 116 coefficient/challenge limb bounds.

`R1Z.PV_Canon.op121_arguments` (PV_Canon_Prefix) proves:

```
current interpolate values = ok coefficients
current semantic ... = ok (Ok sampled, after)
Array.update point round sampled = ok updated
Array.index_usize updated round = ok read
round.val < 10
------------------------------------------------
Coeffs coefficients ∧ Q read
```

The current dictionary is explicitly `PV_Join_PublicCaller.selected base ops`.
There is no oracle canonicality or entropy premise. Existing interpolation
normalizes arbitrary raw samples before accumulation; the deployed challenge
sampler is the base-P digit sampler, not the legacy rejection sampler.

`round_checked` proves that the **actual extracted one-round caller** equals
its proof-only canonical-domain-monitored copy for round<10. The generated
copy is checked byte-for-byte against the retained extracted body except the
single monitored op121 call. `checked_rounds`/`checked_prover` definitions are
audited, but no recursive caller equality theorem is credited.

`reached_canonical` (PV_Canon_Deployment) composes the local source facts:
`P_NativePrefixBinding base ops reached` implies every reached pair satisfies
Coeffs and Q. The P binding contains source return equations, not a canonicality
field. It is **not discharged** for the installed native caller.

## Producer inventory and status

| Producer | Checked result / boundary |
|---|---|
| reduce_u64 | `current_reduce`, `checked_reduce`: every u64 input returns <P. Nat two-fold bounds, subtract bound, exact modulo-P result also proved. |
| M31 constructors/constants | Raw constructor has no unconditional invariant; bounded samples, zero, one, half/quarter constants proved. D234 and P itself are excluded. |
| CM31/QM31 lifts | `lift_complex`, `lift_quartic` on the read-only PV_Ext extraction. |
| M31 add/sub/mul/neg | Canonical closure proved on the named extracted current definitions; mul canonical even for raw u32 inputs. |
| CM31 arithmetic | add/sub/mul/neg, square, scalar multiplication, double, mul_by_r checked. |
| QM31 arithmetic | add/mul/neg, square and scalar multiplication checked. QM31 sub reuses `ProverCommitNativeQ48.sub`; see reused-qsub.json. |
| Prepared multiplier | Constructor components, constructor result, component multiply and full multiply range checked. |
| Inversion | Successful owned fixed-chain and interpolation inverse, scalar try-inverse, CM31/QM31 try-inverse ranges checked. No witness-independence or zero-event mass claim. |
| Deserialization | Successful M31/CM31/QM31 parsers produce canonical representatives. |
| Transcript | Base-P sampler total and canonical for arbitrary 32-byte blocks; current semantic successful return canonical; exact update/read transport checked. Legacy mask/reject shape separately checked. |
| Polynomial | Existing extracted current interpolation result reused and instantiated, including arbitrary raw sample inputs. |
| Installed caller | P_NativePrefixBinding / P_installed remain open; exact frozen stack and locations in INVENTORY.md and OBLIGATIONS.md. |

`d234_not_quartic`, sampler/parser exclusions, and `semantic_ne_d234` formally
exclude the retained noncanonical challenge on the checked source paths.
No deployed noncanonical op121 event was found. The retained D234 example is
not reported as a deployed counterexample.

## Exact remaining op121 row obligation

`P_op121 shipped` is complete Result equality, on Coeffs/Q inputs, to the owned
Horner evaluator over the named extracted field operations. `op121_law_iff`
proves it is equivalent to: for every canonical 28-coefficient polynomial and
challenge, shipped returns `ok z`, Q z, and decode(z) equals its polynomial value.
Horner totality, canonicality, field meaning, and canonical representative
injectivity are proved. This does **not** prove the shipped radix-four source law.

Still required: an accepted extraction or structural/Lean source link for the
frozen radix-four body, including fused three-product reduction, block indexing,
squares, prepared multiplication, and the six combining steps. Route (ii) is
only a candidate; no source rewrite or adoption occurred.

## Native and cohort boundaries

The frozen stack is prover.rs:159 → host_semantic::build_with_material →
host_sumcheck::prove_sumcheck (host_semantic.rs:151) → op121 (host_sumcheck.rs:73).
The oracle closure, input checks and argument producers are inventoried.
The installed records association is still a P6 candidate on the pinned
read-only RunJoin evidence. See SOURCE-BOUNDARY.md: the P7 current/ct extraction
is a candidate cohort, not silently identified with this checkout's frozen field.rs.

## Validation and stop

Budget exhausted: **100/100 Lean** (74 pass, 26 rejected); **6/6 Kani** (5 solver
passes covering six control/index checks, one CLI rejection before compilation).
All host jobs used 6G/8G/swap=0/TasksMax=64; Lean -M7000. All reported swaps zero.
Kani used optimized compilation and no chained field arithmetic or stubs.

Final audit source revision: `3beca9183d1735cbdbd58fc8d22f63a99eebf473`.

| ID / target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| 44497 / R1Z/PV_Canon_AuditA | 0 | 4.006647492 | 4,281,632 | 0 |
| 44498 / R1Z/PV_Canon_AuditB | 0 | 4.578484134 | 4,293,636 | 0 |
| 44499 / R1Z/PV_Canon_AuditFinal | 0 | 3.145232364 | 4,297,924 | 0 |

All 120 final reports (116 theorems, four monitored definitions) use no axioms
or a subset of propext, Classical.choice, Quot.sound. Exact per-attempt targets,
revisions, source/import hashes, exits, wall, RSS, swap and full axiom output:
receipts.jsonl, FINAL.json and numbered receipt directories. The accepted closure
uses retained dependency objects; this is not a fresh coherent release rebuild.

Recursive transport attempts hit kernel normalization/memory failures; no cap
was raised or unchanged failed job rerun. ROUNDS-MEMORY.md records the failed
replacement. Four unaccepted sources are retained under unsubmitted-drafts,
excluded from the accepted source/audit closure. The small RoundVisit theorem is
a control-model invariant, not a recursive source association.

Next deliverable: prove the recursive extracted call-event/prefix transport
without normalizing the large fixed-point proof, then bind it to the installed
RunJoin caller; separately obtain the approved op121 source-law extraction/link.
