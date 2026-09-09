# C1-only coefficient recovery without a final-distance condition

Research base: `113dc5dacbf630c234cc6498385913507c171f8f`.
Main was inspected read-only at `544e366ddcde2646a6799edf95e6879cd459984d`.
The imported V7 source closure remains pinned to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; no new main K13 leaf is imported.

## New deterministic endpoint

`EarlyC1GaoRecovery.early_failure_reduction` is kernel checked. From the
**literal** `earlyC1 received = some p`, it derives a common bad-fibre set of
size at most 16,535. The support follows from the existing optional object's
definition, not a new membership or acceptance assumption.

For any embedding of 513 distinct fibres into the actual 262,144-fibre
domain, failure of the defined decoder to recover all sixteen semantic
columns implies that at least 129 sampled fibres belong to that same bad
set. This holds independently of the final polynomial, its distance, C2,
gamma and relation acceptance. It therefore applies to the coefficient
recovery portion of far-final executions whenever the early object exists.

The decoder's inputs are the received word, the sample and public algebraic
data. The candidate `p` is **not** an input. `sampledIndex` uses the existing
source-shaped `fibreEmbed(fibre,slot)=4*fibre+slot`; the proof establishes
injectivity of all 2,052 sampled symbol indices. The common-fibre Gao theorem
is used once for all sixteen columns, without a column union.

| New declaration | Exact contribution |
|---|---|
| `badFibres_card` | The populated C1-only optional object implies a common bad set of size ≤16,535 |
| `sampledIndex_injective` | Distinct selected fibres give 2,052 distinct actual stored indices |
| `sampleSet_card`, `sampledBad_card` | Ordered samples and their 513-element subset have the same bad count |
| `sampled_outside` | Actual fixed C1 samples outside the common bad set equal the recovered original-code evaluations |
| `failure_requires_129` | Consumes arbitrary-word Gao completeness; decoder failure requires ≥129 bad sampled fibres |
| `early_failure_reduction` | Combines the populated optional object, common support and actual sampled decoder |

`GaoRecovery.decoder_complete` already proves completion of the specified
Euclidean procedure with fuel `n`; it does not assume that a decoder returns
successfully. Here `n=2052`. This finite-fuel mathematical polynomial model
is in a noncomputable section. It is not an extracted Rust algorithm, a wall
time bound, or proof that the actual rewind process exposes these values.

## Remaining interfaces and the right event

The new theorem retains explicit, public algebraic interfaces:

- natural-tensor evaluation equals the actual `exactInitialEncoder` at
  every stored index;
- the supplied circle coordinates and parameter map are valid/injective;
- the public target evaluation matrix has the supplied left inverse;
- the field constants satisfy the required square-root/half identities.

These are not placeholders for decoder success, payment validity or code
membership of the received word. They are nevertheless uncompleted concrete
source interfaces and must not be assigned tiny error probabilities.

The result currently recovers QM31 message coefficients from a QM31-valued
received C1 function. Canonical M31 descent, raw-byte authentication and
actual extractor/source refinement remain separate. Correct coefficients
alone do not prove the selected semantic/copy/path constraints or return a
checked payment witness.

The useful subsequent probability event is joint **accepted coefficient
recovery failure**, using a fresh private uniform 513-subset of this fixed
word. It is not a conditional law obtained after accepting a proof, and it
does not identify all provider `none`/abort/fuel outcomes with the optional
mathematical object. The root continuation supplies the separate finite
subset counting/acceptance composition. No hypergeometric calculation or
unchanged Gao proof was replayed in this subtask.

The root's now-checked `EarlyC1SampleGame.accepted_coefficient_failure_bound`
consumes this decoder implication through a canonical ordering of the
private subset. `PrivateSampleMoment` gives the exact upper bound

`choose(16535,104)*choose(262144-104,513-104) / (choose(129,104)*choose(262144,513))`,

approximately 134.453 bits. It permits an arbitrary acceptance predicate
because accepted coefficient failure is a subset of coefficient failure;
it does not condition uniform sampling on acceptance. This is a private
extractor sampling bound under the public algebraic interfaces and present
early object, not proof soundness or an actual rewinding theorem.

The still-open global alternatives include absent early C1 with failed
checked extraction; present early C1 with invalid/unbound payment semantics;
authentication/access/replay failures; and canonical/source/refinement
failures. Successful extraction, in any final-distance regime, contributes
zero to the desired failure event.

## A smaller classifier obstruction: all C1 is not semantic C1

The source declares sixteen semantic C1 lanes and ten mask-only lanes, with
the mask-only region starting at lane 16 (`state_only_hiding.rs`, constants
at lines 12–25). Thus absence of a close **26-lane** tuple does not establish
failure to recover the semantic projection.

The exact tiny control [early_c1_projection_control.py](experiments/early_c1_projection_control.py)
exhausts all 49 two-lane constant-code tuples over F7 for one fixed received
word on twelve fibres. The semantic lane is constant 5, the helper lane is
1 on three fibres and zero elsewhere, and the cutoff is two. No all-lane
candidate exists, but the semantic codeword is uniquely determined. This
falsifies the bare classifier implication; it is not a circle-code,
verifier-acceptance or payment-forgery experiment.

The same geometry is available conditionally in the selected code: start
with a codeword tuple and change only one mask-only lane on 16,536 complete
fibres. Its original mask codeword is just outside the 16,535-bad cutoff.
Any distinct mask codeword has distance at least
`262144−256−16536=245352`, by the proved pairwise complete-fibre overlap cap.
Consequently there is no qualifying 26-lane early tuple, while all sixteen
semantic lanes are unchanged. This is a symbolic code-word construction,
**not an executed valid-payment proof**. In particular this report does not
assert a full source acceptance probability for it. A future same-execution
control must commit the corruption before early challenges and run the
semantic producer, helper construction and repaired proof causally.

This means that early C1 existence is a useful sufficient classifier, not a
necessary definition of successful semantic or payment extraction. Do not
replace the global failure event by `earlyC1 = none`.

## What current V7 work can actually supply

The newest inspected committed main theorem,
`V7Tag73K13CandidateDirectedOperationalClosure.exact_tag73_preQ16_operational_k13_candidate_directed_probability_le`,
has advanced beyond the old untracked scheduler sketches. It integrates
candidate-directed query-batch resource accounting. Its theorem still
requires `ExactCandidateDirectedK13ViewAlignment`, a restricted later-alpha
source, an exact decoder instantiation, the operational source environment,
and exposure/resource bounds. It bounds its specified V7 K13 event, not
general C1/payment recovery, and K14 width29 remains a separate event.

`V7CandidateChainExtraction.accepted_selects_one_consistent_chain` remains
useful finite-chain logic, but its q16 raw-word `IdealAccepts`, list-decoder
completeness/output bounds, and explicit query/fold/list-failure exclusions
are not the q22 quotient matching experiment. The existing `U=1,I=1`
raw-versus-quotient fold falsifier still rules out substituting the V8 final
into that old definition unchanged. No old numerical error or q16 cap is
reused here.

The present bridge instead reuses the proved V7 original encoder/own-support
interfaces and the existing arbitrary-word Gao completeness theorem. It
does not depend on newer main declarations or falsely treat them as an
acceptance-to-C1 coverage certificate.

Read-only main source hashes at the stated commit:

| Source | SHA-256 |
|---|---|
| `V7Tag73K13CandidateDirectedOperationalClosure.lean` | `b3c19dc01deeee1193ddf4c558ad5b9b8fa572539492161cc9c4b90bd8dc1c18` |
| `V7Tag73K13CandidateDirectedSourceBridge.lean` | `6e008dcff45a2fd9dd3e30dc00b17d463151e353a788a942fe4aac737bf2d017` |
| `V7CandidateChainExtraction.lean` | `d8388985004eb8995dbc1870d1d1099f0bb1325d4618eab073bb28626456377e` |

## Evidence and costs

The focused changed leaf passed on Lean 4.32.0 / Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, with the serial 7-GiB process-tree
guard and `-M7000`. Full imported source/olean provenance is recorded before
and after the successful check in [early-c1-gao-v2.log](experiments/early-c1-gao-v2.log).
All seven audits use only `propext`, `Classical.choice`, and `Quot.sound`.
No new axiom or retained `sorry` is used.

| Run | Exit | Lean wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| v1: local product-projection and predicate-instance elaboration errors | 1 | 17.25 | 5,573,476,352 | 0 |
| v2: corrected explicit projection/decision interfaces | 0 | 11.44 | 5,737,594,880 | 0 |

No cap increase or unchanged replay occurred. Failure logs are retained.
The source and olean hashes are respectively
`55f1af92b6f5e5f7ec62b972619cad5a571a73db719775de8d32b1e1a837a723`
and `6fd84d8403439d8fd1bbbdcaa4e4ab666f5895d2840203a9ad60128c4b2e9d7f`.

Reproduction from the research worktree, choosing an unused log filename:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_gao.sh /tmp/early-c1-gao-recheck.log
python3 docs/research/v8-no-work-100-20260907/experiments/early_c1_projection_control.py
```

The ideal sample provides 2,052 positions and 32,832 semantic field values.
Materializing all 26 lanes as unpacked four-byte M31 limbs would occupy
`513*4*26*4 = 213408` bytes. This is not the serialized leaf payload:
the source packs those values into 403 bytes per leaf, or `513*403 = 206739`
bytes; adding each 32-byte salt gives `223155` bytes before authentication,
indices and framing. These are **extractor access/representation counts**,
not proof-body bytes, verifier CU, measured network traffic or measured
extractor runtime. The root alone does not supply these evaluations. The
proof body remains 40,282 bytes, with no new protocol messages, checks,
transcript calls or security credit from work.

## Decisive next experiment

The most consequential missing implication is now **far accepted wrong
semantic-C1 point binding even when the early object exists**. Fix C1 and its
coefficient object before lambda/chi; fix an incorrect semantic-lane point
claim before gamma; allow legally adaptive C2, both OOD vectors, relation
responses and far finals. A useful next causal small-code search and
symbolic theorem must bound, or falsify a proposed bound for, that joint
accepted event using the image/shifted-row/query grammar. A false claim for
this particular coefficient object is not automatically a payment forgery.
Completing the public encoder/matrix interface in parallel is valuable, but
cannot replace this missing acceptance-to-semantic-validity argument.
