# Verification performed in the packet environment

Date: 21 September 2026. Base repository head rechecked as 77fb7872. No repository
writes or deployments were performed.

## Executed

`python run_checks.py` compiles `tests/checks.cpp` and `tests/channel_fold.cpp`
with `g++ -std=c++17 -O2 -DEXTENSION` in a temporary directory and executes both.
Assertions remain enabled; the retained model rejects NDEBUG builds. Both
checks passed. Machine-readable results are in `executed_checks.json`.

| Test | Count/result |
|---|---|
| Factored fixed-map correction | 192 full-QM31 cases |
| Independent full chord/adjoint cross-check | 24 cases |
| Query sharing | 96 cases, including rho=0,1,-1 |
| Query states before/after folds | 384 checks |
| Quotient and four-slot fold linearity | 1,024 cases |
| Canonical word arithmetic | 200,049 cases |
| Error controls | Wrong query scale, wrong channel split, overgeneralized one-fold reducer detected |
| Full channel-weight algebra | 48 cases, beta=0,1,-1 and general QM31 |
| Channel weights after four folds | 192 checks |
| Quadratic false-boundary errors over F31 | All 28,830 polynomials; at most two roots |
| Fixed-map coefficient table expansion | Exact signed equality over integers |

The arbitrary quotient tests do NOT zero the image residual coordinates.
The 1,024 opening tests are algebraic, not byte parser or authentication tests.
The finite F31 experiment is a check of a mathematical root-count lemma, not a
probability experiment over the actual source oracle.

The canonical multiplication fast path is deliberately narrower than a general
u62 reducer. For x=2^62-1, one fold and one subtraction leaves P (noncanonical),
so general reduction must remain unchanged. The negative control enforces this.

## Model provenance

`tests/model.hpp` retains the independent M31/CM31/QM31 and natural-basis chord
model from the supplied R18 packet. That provenance is recorded in
`SOURCE_PINS.json`. This is not a Rust extraction, a production fixture, or a
claim that the R18 compiler correspondence has already been established.

The T163 generator uses the retained inventory and separately requires the
literal current staged ORDER to match before Rust integration. The real stage
inventory gate has NOT been run in this environment, which has no local clone.

## Not executed / not proved here

No Rust, Cargo, Lean or Lake executable is available. The Rust files and six
Lean scalar leaves are drafts. No Rust compilation or Lean axiom audit is
claimed. No SBF/LiteSVM build or run was performed. No claim of a new CU number,
supported-budget verification, full source correspondence, global soundness,
full privacy, or release suitability follows from this packet.

The cost figures in `source_reported_cu.json` are from the pinned repository
report, not new measurements. The degree-two 2/|F| soundness step is conditional
on a fixed pre-challenge pair and a suitable challenge law; those are not
established by the local tests.

## Archive integrity

The final manifest records each payload file's SHA-256 and length. The archive
is freshly extracted and its checks recompiled/reexecuted before delivery;
that external delivery record is supplied beside the ZIP.
