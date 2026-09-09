# Fixed-C1 far-final relation-compatible reduction

The kernel-checked endpoint concerns the actual mathematical repaired relation game with an early C1 object and arbitrary three received helper lanes. It retains an adaptive final after the first folding challenge. It does not give a numerical bound on accepted far-final wrong claims.

## Exact residual event

`FixedC1FarMoment.Execution` fixes received C1, `earlyC1 c1 = some p`, received C2, both OOD answers and ordinary point claims before gamma. C2 can have depended on earlier semantic/copy challenges. The inactive claim depends on gamma but precedes kappa. The inherited strategy receives gamma and kappa; its first response depends on tau but not alpha, its final depends on tau and alpha but not queries, and later compact responses follow their actual causal grammar.

The event is a wrong ordinary or OOD C1 claim against this same early `p`, together with more than 15,334 disagreements between the actual chosen final and the actual folded virtual quotient. It is not absence of a nearby anchor, provider failure, invalid payment semantics, or failure of every possible extractor.

The virtual quotient is exactly `SelectedComponentGame.received c1 c2 data gamma`. No raw-word V7 consistency definition is substituted for its actual folded matching set. `oracle 0` packages that word with full-domain corruption support; the reference zero vector supplies no polynomiality or recovery assumption.

At the full pre-query prefix let `c` be the carried prior against the actual final, and let `M` count matching final-domain points. The remaining moment is the original sequential average of

`1[wrong C1 claim and far final] * 1[c = 0] * choose(M,q)/choose(T,q)`.

The new relation-suffix theorem gives the bound by this moment plus `q/|G| + 18/|A|`. The numerator q is the shifted batch's genuine degree, not q−1. The 18 counts only the three later degree-six relation repairs. Image mixing, shifted ordinary rows and the first relation response remain inside the moment; they are not silently assumed correct or separately charged again.

## Gamma-level reduction

One wrong C1 claim selects one actual ordinary/OOD functional and its 29 claims before gamma. For any fixed helper message triple `h`, join `p` and `h` to obtain the full 29-message tuple. Its selected claim-error polynomial `E_h` is nonzero because the wrong C1 coefficient remains unchanged, and it has degree at most 28. There is no 145-claim union and no assertion that `h` represents the received helpers.

`fixed_claim_far_reduction` charges at most `28/|Gamma|` for roots of this fixed polynomial and retains the relation-compatible moment only for `E_h(gamma) != 0`:

`Pr[far and wrong-C1 and relation accepts]`

`<= 28/|Gamma| + outsideRootMoment(E_h) + q/|G| + 18/|A|`.

The unknown moment remains symbolic. The error polynomial can be chosen from any fixed helper triple, not from a helper representation selected after the sampled gamma. This is an unconditional finite averaging reduction, not a probability after conditioning on image/row correctness.

For an arbitrary helper triple, excluding its roots is bookkeeping until a coverage or relation-constrained argument links that triple to the actual far candidate. Nonvanishing of `E_h` alone does not force the actual carried prior to be nonzero: the latter is evaluated against an independently adaptive final. Thus the displayed root charge is not new evidence that the remaining moment is small.

## What the helper degree does, and does not, establish

The source scalar-power received helper curve is proved degree at most two at each stored symbol. On C1's own support, the raw batch equals the known encoded C1 batch plus gamma^26 times that quadratic helper curve. All excluded C1 fibres remain in the actual game and matching count. An early object is not used to replace received C1 globally by an exact codeword.

This degree-two structure is input to the missing theorem about `outsideRootMoment`; it is not yet used to bound that moment. The full claim-error polynomial remains degree 28, and wrong OOD answers retain their reciprocal-power contribution after quotient normalization. No punctured-code membership or bounded covering family is assumed.

The decisive next lemma must bound the relation-compatible far agreement moment for this specific helper curve and actual final-dependent transported functional. A family argument would need to establish coverage first. Choosing only zero-prior finals without charging the other suffix events is invalid: the retained F19 strategy control has states where unrestricted far finals outperform that restriction. The present reduction charges nonzero-prior acceptance through rho/later collisions and does not make that restriction.

The target requires a further distinction: `farWrong` compares claims with
one early C1 object; it does not express failure to return every checked valid
payment witness. A reconstructed alternative codeword must be passed through
the payment endpoint before its branch can be counted as extraction failure.
Consequently bounding the entire far moment is a sufficient route, not a
necessary security claim. The [continuation](far-final-continuation.md) keeps
the accepted failure of a specified extractor as the final event and examines
coherent multi-fork recovery as an alternative to suppressing the whole moment.

## Scope, provenance and costs

The source and evidence are in `experiments/FixedC1FarMoment.lean`, `run_fixed_c1_far_moment.sh`, and the versioned `fixed-c1-far-moment` logs. The runner checks the entire imported research/source closure against research commit `edb199c12fcc41f00330298b95b4736f60ac6f3a` and borrowed immutable V7/source commit `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. `RelationCompatibleMoment` is a separately pinned new dependency. Reuse includes the actual selected encoders/own-support object, raw scalar batch, reconstructed row/image prefix and compact ordered relation suffix; it does not reuse V7 numerical recovery caps outside their hypotheses.

The initial replay failed on two local elaboration errors, not a false statement: missing namespace for rawBatch and a no-progress simplification tactic. Version 2 exposed an ambiguous field alias from opening that namespace; version 3 uses the fully qualified rawBatch name. Both exit-1 logs remain retained. There was no memory-cap increase or unchanged replay.

| Focused target | Exit | Wall time | Peak RSS | Swap | Audit |
|---|---:|---:|---:|---:|---|
| FixedC1FarMoment v1 | 1 | 28.77 s | 5,404,540,928 B | 0 | Failed elaboration; not retained as a proved endpoint |
| FixedC1FarMoment v2 | 1 | 33.22 s | 5,560,745,984 B | 0 | Failed namespace resolution |
| FixedC1FarMoment v3 | 0 | 25.31 s | 5,599,363,072 B | 0 | All ten audited results use only propext, Classical.choice, Quot.sound |

The exact successful source SHA-256 is `ff5c7d07af65b14c9040080da36cac25c09867061b645ad2e3081d45234a671b`; its olean SHA-256 is `4b7fc5481cf64fb7bd9081d8a22960247c772104d20854efa0c5ac9c7a5382bc`. The source was frozen after this replay. The runner uses Lean 4.32.0, `-M7000`, an aggregate 7-GiB RSS guard, cached dependencies and before/after provenance checks; the reported wall time is the Lean leaf, not shell provenance traversal. No new axioms or `sorry` occur in the retained leaf.

The replay command, from the research root, is:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_fixed_c1_far_moment.sh docs/research/v8-no-work-100-20260907/experiments/fixed-c1-far-moment-v3.log
```

The runner deliberately refuses to overwrite an existing log; a justified future replay must supply a new evidence filename.

| Result | Exact implication |
|---|---|
| `raw_on_own_support`, `helper_degree` | Actual raw received batch has the fixed-C1/quadratic-helper form on the own support, with excluded fibres retained |
| `joined_error_nonzero_degree`, `wrong_claim_polynomials` | One fixed incorrect C1 claim survives every joined helper triple as a nonzero degree-at-most-28 polynomial |
| `slice_bound`, `far_wrong_reduction` | Actual adaptive compact suffix acceptance reduces to the compatible moment plus rho/three-later-round errors |
| `fixed_claim_far_reduction` | Charge at most 28 gamma roots and keep the unknown far compatible moment restricted to nonroot gammas |

The ideal construction is over fixed mathematical received words and explicit uniform finite challenge averages. It is not a translated Rust verifier, a statement that Merkle roots supply total words, or an actual replay extractor. The totalized virtual quotient keeps every domain point in the model; a deployed parser's zero-denominator rejection must be connected separately, not assigned a fabricated error probability.

No proof-body values, challenges, operations, production code or verifier checks are added. The 40,282-byte body model is unchanged. This run has no SBF, complete-transaction CU, proving-time or extractor-runtime measurement. Full-view ZK, Fiat–Shamir/retry resources, authenticated-word/replay coupling, early-C1-none cases, semantic validity and checked payment-witness extraction remain independent obligations. No global security total is inferred from the displayed symbolic reduction.
