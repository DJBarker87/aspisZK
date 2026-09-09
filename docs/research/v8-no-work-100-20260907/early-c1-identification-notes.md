# Concrete early-C1 identification continuation

Status: the new arbitrary-set exact-code interface and concrete named
agreement cap are kernel-checked. The concrete optional-object application
still does not have a completed Lean replay; the last bounded importing
leaf was stopped by the memory guard. It is retained only as draft text.
The preceding committed generic uniqueness, exact V7 fibre cap and optional
early-C1 definition remain unchanged.

Research base: `5e26df14ad5fc674d5ea43d02431f1dc9ef682fa`.
The runner pins all 78 transitive Aspis source imports against this revision
and the cache workspace, logs source/olean SHA-256 values, and uses Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` / Lean 4.32.0.

## Completed interface and still-missing endpoint

`EarlyC1Identification.lean` proves three declarations:

- `agreement_cap_from_sets` is a generic adapter from a cap for arbitrary
  supplied matching sets to the existing generic agreement definition.
- `matching_set_cap` proves that any supplied set of complete fibres on
  which two distinct exact V7 circle-code messages agree has cardinality
  at most 256. It constructs the containment in the already-proved exact
  full-fibre agreement set; it assumes neither candidate membership nor a
  provider result.
- `exact_agreement_cap` specializes that adapter to the actual
  `fibreEncode` and the existing generic `agreement` object.

This closes the concrete cap interface without comparing independently
built concrete filtered enumerations. The cap itself is reused mathematics,
not a stronger distance estimate or new security bits. It still does not
complete the following intended specialization.

For the actual circle encoder and received C1 word, any 26-column message
tuple agreeing on at least 245,609 complete fibres equals the optional object
defined from that received C1 word alone. This would identify the C1 part of
a late near-gamma tuple with a pre-lambda/chi mathematical object without
assuming provider success, without retroactive fixing, and with the `none`
branch retained. It is not executable extraction, acceptance coverage, or
payment validity. No new numerical security term is proposed.

## Focused changes and failed checks

| Variant | Mathematical/interface change | Exit | Wall | Peak RSS | Swap |
|---|---|---:|---:|---:|---:|
| v1 | Locally opaque finite-container operations while applying the concrete cap | 137, aggregate guard | 33.95 s | 7,845,429,248 B | 0 |
| v2 | Generic transport with the source filter's explicit predicate decision | 137, aggregate guard | 10.43 s | 7,747,862,528 B | 0 |
| v3 prefix | Arbitrary-set interface; isolated missing classical decision and a reserved binder name | 1 | 6.73 s | 5,511,249,920 B | 0 |
| v4 prefix | Local errors fixed; generic adapter and concrete arbitrary-set cap | 0 | 13.66 s | 5,617,598,464 B | 0 |
| v5 | Restored cap plus optional-object application in one leaf | 137, aggregate guard | 15.60 s | 7,624,015,872 B | 0 |
| v6 cap | Cap-only localization; all cap proofs checked, orphan doc-comment syntax error | 1 | 2.96 s | 5,513,641,984 B | 0 |
| v7 cap | Orphan comment fixed; final retained cap leaf | 0 | 3.27 s | 5,657,886,720 B | 0 |
| v8 endpoint | Separate importing leaf; explicit type arguments, no `unfold earlyC1` | 137, aggregate guard | 9.50 s | 7,733,198,848 B | 0 |

The guarded runs are resource failures, not counterexamples. The third reached
the import and emitted ordinary local elaboration errors without approaching
the guard. No failed variant is a retained theorem. They were not rerun
unchanged or given larger limits.
Both use `-M7000` and a separate 7-GiB aggregate-process guard sampled each
second; this sampling explains the small reported peak overshoot. The exact
commands, input hashes and import provenance are in
`experiments/early-c1-identification-v1.log` and `-v2.log`.

The new interface separates an arbitrary supplied support set from computed
agreement filters: the exact V7 cap bounds any set whose fibres match, then
a generic adapter supplies the previous generic theorem's cap. These two
declarations passed v4, and the concrete cap application passed v7, all with
only `propext`, `Classical.choice`, `Quot.sound`. No new axiom or `sorry` is
present in retained claimed results. The optional-object theorem is commented
out in the cap leaf and its isolated variant is in
`EarlyC1IdentificationEndpoint.draft.txt`; neither is a completed result.

This gives a more precise failure localization than the previous run: the
exact circle cap and its generic-agreement interface now elaborate cheaply;
the resource problem remains in specializing `early_eq_of_large_support`
to the existing concrete `earlyC1` object. Merely moving the cap behind an
import boundary and removing `unfold earlyC1` did not close it. No single
internal normalization cause is claimed established. In particular,
`c1_margin` already has the symbolic `Fintype.card (Fin 262144)` statement,
proved via `Fintype.card_fin`; this is not a request to evaluate that cardinal
by concrete enumeration.

## Final evidence and reproduction

The final retained source was not edited after the successful v7 replay:

| Artifact | SHA-256 |
|---|---|
| `EarlyC1Identification.lean` | `32ef2238dd3375706b38142eabb036814aaedefa2efdd8a1753518e2e1efcc35` |
| `EarlyC1Identification.olean` | `61baa62ab02479b9723388d086a4c33b1791afb970a28864ae1d1a65c5a1e22d` |
| Current runner | `ba60f309035cfc4068a8b8f5ef3e1516cd1cd27c311ea94f12e6f401fd8dff5f` |

The runner gained a second, diagnostic target argument for the v8 attempt;
its default cap command is unchanged. The diagnostic endpoint is now text,
so it is deliberately not replayed as a retained `.lean` result.

From the research root, with a new nonexisting output log:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_identification.sh \
  docs/research/v8-no-work-100-20260907/experiments/early-c1-cap-replay.log
```

The runner checks all 78 transitive Aspis source imports against the pinned
research source and the advancing cache workspace before and after a
successful proof. The compiled V7 source reused here is
`V7C1ConcreteProjectionBinding.lean` (SHA-256
`78571066d66be07ccfbd526d36be9515be60920cbecc416da467fff44ba1f6e3`),
through `NearGammaFibreBridge`'s actual four-slot map and exact overlap cap.
Its olean SHA-256 is
`21dc55087ce72888fcb2c24600f06cf484bfadf4b4f4462109f7807147c9e960`.
The complete source/olean inventory is in each log. Main remained read-only
at the recorded `94459d0f9700388431c26c1261fbfa6974118af0` during these runs.

## Unchanged boundaries

The totalized C1 mathematical word is an explicit input, not data obtainable
from a Merkle root alone. The source V7 totalization lemma does not weaken
canonical opening rejection. The optional object is noncomputable and does
not fix an efficient decoder, fork budget or oracle access model. A missing
candidate is not silently zeroed. The exact-code near-gamma instantiation,
actual accepting-source implication and early semantic challenge binding
still require their separate bridges.

No Rust, SBF, transcript, proof body, production acceptance or CU changed.

The next C1-specific diagnostic should inspect the fully explicit implicit
instances of the concrete optional definition and generic theorem before
another proof run, then stage the specialization over an opaque support
predicate/cardinality interface. It must not change the optional object,
assume a populated option, or raise the memory cap. Actual late width29 lane
restriction, base descent and acceptance/recovery composition must not be
reported complete just because the cap interface is now available.
