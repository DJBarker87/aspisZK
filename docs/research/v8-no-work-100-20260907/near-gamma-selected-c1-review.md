# Concrete gamma coverage identifies the earlier C1 object

Research continuation from `51b78cbf7fadee4ec70328c86add7678a43f21da`.
No verifier, wire, production, main-branch or deployment change.

## New result

The generic near-gamma theorem is now instantiated with the selected
mathematical original-code encoder, the literal scalar-power curve of
26 fixed C1 lanes plus three arbitrary later C2 lanes, and the existing
source fibre map. The dense branch returns **message coefficients**, not
only an abstract family of codewords.

`NearGammaSelectedC1.selected_gamma_c1_dichotomy` proves, for each fixed
C1 word, arbitrary C2 word and fixed allowed gamma set G:

* Fewer than 64 gammas in G have a 9,301-close original-code candidate; OR
* There are 29 original-code messages p with at least 245,609 complete
  fibres of joint component agreement, `earlyC1 c1 = some (c1Projection p)`,
  and every 9,301-close candidate at every gamma in G is the encoding of
  the coefficient batch `sum gamma^lane * p[lane]`.

The tuple is constructed by the existing interpolation dichotomy and
linear-map range witnesses. It is not passed in through candidate membership,
a decoder-success assumption, or equality with an honest fixture.
`no_early_c1_forces_sparse` retains the absent-early-C1 branch explicitly:
if the C1-only optional object is none, the dense branch is impossible for
every choice of later C2.

The final `NearGammaSelectedCoefficients.raw_message_cover_dichotomy`
strengthens encoded-word equality to **literal message-coefficient equality**:
in the dense branch, for every gamma in G and every original message m,

```
(fibreBad (exactInitialEncoder m) (rawBatch c1 c2 gamma)).card ≤ 9301
    implies m = sum_lane gamma^lane • p[lane].
```

Encoder injectivity is proved from the actual overlap cap and domain size.
The reversed mismatch orientation and exact child-index/fibre-embed
correspondence are proved, rather than silently substituting raw-word and
quotient matching sets. Membership in the original code is automatic for
the encoded message m, not an additional provider-membership premise.

The C1 object remains the unchanged object defined from C1 alone. The full
tuple is fixed after C2 but before gamma; only its C1 projection is identified
with the earlier object. This is not permission to move all C2-dependent
coefficients before lambda/chi.

## Exact encoder and support interfaces

| Result | Interface established |
|---|---|
| `NearGammaMessageCover.curve_coeff`, `curve_eval`, `curve_degree` | The degree-28 polynomial's coefficients are exactly the received component words and its evaluation is the scalar-power batch |
| `message_cover_dichotomy` | Constructs coefficient messages from the code-valued cover and transports its actual own support |
| `NearGammaSelectedC1.fibreLinear` | Reuses V7's proved linearity of the exact log-20 original-code evaluator, packed by `fibreEmbed` |
| `domain_card` | Symbolic cardinality transport for the exact existing finite-type instance, without expanding 262,144 elements |
| `curve_eval`, `near_encoded_iff` | Relates the concrete raw batched component word to the near-gamma predicate in source fibre order |
| `selected_gamma_c1_dichotomy` | Combines the constructed tuple, actual own support and unchanged early C1 optional object |
| `no_early_c1_forces_sparse` | Explicit accounting of the no-candidate branch |
| `NearGammaSelectedCoefficients.fibreEncode_injective` | Actual original-code coefficients are determined by their fibre word |
| `fibreBad_raw_eq`, `near_of_fibreBad` | Exact raw mismatch set enters the near-gamma predicate with the correct slot map and orientation |
| `raw_message_cover_dichotomy` | Every qualifying original candidate's coefficient message equals the fixed pre-gamma component batch |

The exact original-code range is used. It is not replaced by an ambient
Reed–Solomon code or by the quotient's full polynomial space. The source map
is `(fibre,slot) -> 4*fibre+slot`; the old `NearGammaFibreBridge` proves its
connection to the selected index convention. Reused overlap is 1,024 symbols
and therefore 256 complete fibres. No list-of-100 union is introduced.

V7 reuse is limited to mathematical encoder linearity, exact-domain overlap,
and the previously checked support/early-object results. In particular, this
does not import the older work-normalised security ledger or a new candidate-
directed theorem from concurrent main work.

## Evidence and reproduction

Run from the research worktree, using the existing pinned local cache:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_near_gamma_selected_c1.sh \
  /tmp/new-near-gamma-message.log NearGammaMessageCover
bash docs/research/v8-no-work-100-20260907/experiments/run_near_gamma_selected_c1.sh \
  /tmp/new-near-gamma-selected.log NearGammaSelectedC1
bash docs/research/v8-no-work-100-20260907/experiments/run_near_gamma_selected_c1.sh \
  /tmp/new-near-gamma-coefficients.log NearGammaSelectedCoefficients
```

These are focused leaves. Do not rerun unchanged results merely to repeat
the evidence. The original NearGamma and JointImageGame oleans were recovered
from their recorded `/tmp` caches and verified against the published local
evidence hashes, so no unchanged near-gamma proof replay was needed.

| Focused check | Exit | Wall time | Peak RSS, bytes | Swaps |
|---|---:|---:|---:|---:|
| message v1 | 2 | Not launched | Not measured | Not measured |
| message v2 | 1 | 23.66 s | 5,463,228,416 | 0 |
| message v3 | 0 | 6.24 s | 5,644,795,904 | 0 |
| selected C1 v1 | 0 | 14.64 s | 5,701,844,992 | 0 |
| selected coefficients v1 | 0 | 5.36 s | 5,709,250,560 | 0 |

V1 stopped at provenance because the runner routed the umbrella import
`Mathlib` incorrectly; no Lean process was launched. V2 had two local proof
errors: missing polynomial evaluation simplifications and a legacy support
predicate-instance mismatch. The latter was repaired with an explicit
classical predicate decision, not by expanding concrete finite objects or
increasing memory limits. All failure logs are retained.

Successful leaves audit only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry` or new axiom is used. The runner checks recursive imported source
closure against immutable main
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, records source/olean hashes before
and after, and enforces a 7-GiB aggregate-descendant RSS guard plus Lean's
`-M7000`. It uses Lean 4.32.0 and mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

Main advanced during this work to
`db4f9063214ff173eda09faf4f559ce28fc09320`; the final leaf still verified
every borrowed dependency's source bytes against the immutable 26a9 pin.
New concurrent main work was neither edited nor imported.

Source SHA-256 / olean SHA-256:

* `NearGammaMessageCover`: `adccfea2cd5fc04d76c35da41eac5b6dbf2a6d97e95adc4a3d3b79713fc51983` /
  `3724783c5e212f9f8f62558706661f41232e6cbe13ec906f89b6a50e11eb4b96`.
* `NearGammaSelectedC1`: `625bd68d1d317ba0738144c6428ebc2773e8ad351791910916349af98d7c2779` /
  `d4c9935d545bd2c0ec80bd9c2542f0a53d3f2fc88b2e267abfaa5e3a64000857`.
* `NearGammaSelectedCoefficients`: `9aab1dfc9dd87abd5bcda57dbdfa3bd5e78f2057b0afbd3495cc0ef697bda6ae` /
  `dd7d72362132e641c89adcef3768e0b40d046f9d673fe4be3c7e5cc3bd0ae61e`.

The specifically reused V7 linearity module has source SHA-256
`3d1ba9d6499d592eabef4df06785a44fc70a4bdb9fa1ccc5e4437b3557e7bff0`
and olean SHA-256
`f24afda43c96c104ac36554b955a1766eecfbaebc85187ae5952a42dbcd9d45d`.

## Scope and next connection

This is mathematical existence and deterministic causal identification, not
an executable finite-resource extractor. Obtaining authenticated fixed C1
values, efficient interpolation/error correction, replay/fork failures and
checked payment-witness recovery remain separate obligations. The root alone
does not supply the total received word used here. Base-field descent and
source/FFT correspondence are not newly claimed by this leaf.

The sparse cardinality can support a 63/|G| probability charge under a
separately justified fresh uniform gamma law. This file proves no additional
probability ledger and makes no 100-bit release claim. It does not erase far
gamma/fold candidates or provider-none outcomes.

The decisive next connection is the image-aware quotient-to-original-code
reconstruction on the same received word, including chord poles, followed
by the fixed-component point-error gamma bound. The dense tuple here supplies
the missing pre-gamma coefficient object and its earlier C1 projection.

The 40,282-byte body census is unchanged. No new protocol values, verifier
operations, proving benchmark, SBF result, or complete-transaction CU result
is produced. Full-view privacy and the resource-bounded Fiat–Shamir lift
remain open; no grinding credit is used.
