# Unified conditional Fiat–Shamir theorem

The 33-round transcript model now instantiates the existing v3 Fiat–Shamir
framework. `UnifiedFiatShamir.soundness_bound` uses the actual prover-plus-
verifier experiment and proves

```
Pr[acceptance and extractor failure]
  ≤ Qtot * maxErr rb.ε 33 + 3 * Qtot^2 / 2^256.
```

The extractor, final decision, round classifier, and its D1/D2/D3 proofs remain
explicit inputs. This is a checked conditional theorem, not an instantiated
100-bit private-spend theorem. In particular, the query factor is retained;
no work or grinding credit is applied, and a per-query coefficient cannot be
reported as an absolute failure probability for arbitrary query budgets.

## Reuse and composition

`UnifiedDecoder` dispatches the previously checked component decoders by the
address's round label. Initialization has a separate parser, proved disjoint
from absorb parsing. All components return the same `List State` interface:
the query component needs the whole advance-state chain, while the existing
single-state components use the previously proved singleton adapter.

| Round | Component |
|---|---|
| 0 | Initialization |
| 1–25 | Semantic rounds |
| 26 | Reseed/domain transition |
| 27–30 | Ordinary opening rounds |
| 31 | Stopped q22 query sampler |
| 32 | Rho |

`UnifiedDispatchAddress.decode_at_first` proves that the first address of
each actual chain selects its component. `UnifiedDispatchCase` composes the
six existing experiment-case theorems. `UnifiedTotalCase` removes the
intermediate restriction on the prover's unused payload slot zero.

The removal is exact. Row zero's protocol message is C1, not `payload 0`.
`UnifiedPayloadZero` proves that replacing this slot preserves every message,
transcript, chain, challenge, and the verifier program, including the final
decision message. `UnifiedCanonicalProver` performs that replacement after
the prover returns, with no oracle reads. Its prover trace and complete
experiment trace are unchanged. Thus the composed theorem applies to any
prover; it only requires that the codec admit one fixed message encoding the
empty row-zero record. It does not assume the original prover emits it.

`UnifiedInj.inj` packages this actual-experiment recovery into the existing
`R0C.V3.Inj3` interface. The two existing collision events are both charged,
using `UnifiedCollision.mass`, at `3 * Qtot^2 / 2^256`. Earlier prover reads
remain in the experiment table and budget.

`UnifiedDecoderBound` dispatches the existing completing-sampler laws and
bounds. For every successful decoded context, it derives the prefix's exact
round length and applies the corresponding fixed-round premise.
`UnifiedChainDensity.chainDensity` then derives the framework's adaptive
decoder-density obligation from the existing `FS2.D2` condition. If no table
makes the fixed prefix doomed, the bad-event indicator is zero. Otherwise D2
applies, and its row error is bounded by `maxErr`.

Finally, `UnifiedFiatShamir.soundness_bound` directly applies the unchanged
`R0C.V3.theorem43`, with the existing chain/read facts and the new injection
and chain-density proofs. No old security theorem's premises are weakened.

## Exact remaining inputs

The final theorem requires the following, rather than asserting them:

- A `Params` instance with `5 ≤ D`, and a public byte string shorter than
  `2^32`.
- The 33 labels matching `UnifiedLabels.label n` (`0xa0 + n`) and a fixed
  message whose encoding is `PublicInitFrame.emptyRecord`.
- An extractor, Boolean final decision, and `RoundByRound'` classifier.
- D1: extractor failure implies the initial prefix is doomed.
- D2: each independent round sampler escapes a doomed prefix with probability
  at most its specified `rb.ε` entry.
- D3: the verifier rejects a doomed final transcript.
- A bound `Qtot` on distinct first reads of the full experiment for every
  oracle.

There is still no concrete unified R1 classifier/decision/extractor instance
discharging those three conditions with the numerical ledger. The old masked
D3 theorem has a different opening tail and cannot simply be applied to the
new schedule. The R1 semantic-prefix and opening/extraction lemmas are
available for constructing the new instance.

There is an additional extraction boundary. The inspected old
`R0FS.extract` (`v8-r0-fs-20261006/lean/R0FS/Protocol.lean`) and
`R0C.SemStatement.extract` (`v8-r0-close-20261007/lean/R0C/SemStatement.lean`)
ignore the oracle table and use `Classical.choose` to return a witness when
one exists. Their failure event is therefore a witness-nonexistence event.
Reusing those definitions would not by itself prove efficient knowledge
extraction from a prover. The unified theorem accepts an extractor as an
argument and supplies no running-time or witness-validity theorem for it.
The private-spend release needs a separate, justified knowledge-extraction
statement and relation correspondence; this checkpoint does not close it.

The Boolean `decision` is another concrete boundary. `FS2.verifier` records
the sampler chains and then returns that Boolean, whereas Rust also calls
the hash oracle during Merkle authentication and checkpoint handling. This
theorem has not yet incorporated those terminal calls or justified the
commitment-time words they authenticate. An oracle-capable terminal checker,
its read budget, and the causal commitment-binding/extraction argument are
needed before source instantiation. See
[`KNOWLEDGE-AND-ORACLE-BOUNDARY.md`](KNOWLEDGE-AND-ORACLE-BOUNDARY.md).

The byte-level Rust correspondence, authenticated checkpoint/account parsing,
settlement refinement, and complete masking/simulator proof remain separate
open obligations. This change contains only Lean proofs and evidence; it does
not change runtime code or transaction costs.

## Verification

All 11 focused targets passed on the pinned NUC workspace, followed by one
combined import/axiom checkpoint. `R1UnifiedFiatShamir-b` passed in 1.53 s
at 3,551,780 KiB peak RSS. `R1UnifiedFiatShamirCheckpoint-a` passed in 1.43 s
at 3,536,428 KiB, with 33 axiom reports. Both used the existing per-job
4G/6G/zero-swap scope; all final reports contain only `propext`,
`Classical.choice`, and `Quot.sound`, or no axioms.

The [sealed evidence bundle](evidence/lean-unified-fiat-shamir-20261014/README.md)
contains exact source and object hashes, all 22 attempts (10 failed, one
superseded success, 11 final successes), resource receipts, time logs, and
runner/environment fingerprints. The base revision is
`c236efcc23b416e76e5f562d587834d79a6c98c3`. The 14 existing runtime source
fingerprints are unchanged. This was a focused replay using the pinned cache,
not a new whole-repository release replay.
