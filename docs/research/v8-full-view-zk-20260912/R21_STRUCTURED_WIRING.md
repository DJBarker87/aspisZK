# R21 follow-up: specialized wiring, measured 14.60M CU

2026-09-22. Continued from local commit
`469df13b91b61ab3c5889e8dc0e9259832c7cf3e`, on
`research/v8-r21-public-arithmetic-20260922`.

The new fixed-wiring evaluator and balanced circuit cut the isolated helper
from **29,796,433 / 29,793,326 CU** to **14,600,544 / 14,600,921 CU**, about
51%. Both real 1M runs still exhaust. The native ordinary/image calculation
costs only **791,311 / 791,499 CU** on the same public field inputs. The helper
remains about 18.45 times more expensive and is **not integrated** into Aspis.

R20's complete verifier remains unchanged at its previously measured
**2,865,333 / 2,866,803 CU**. Neither 29.8M nor 14.6M is a new Aspis verifier
cost. The under-1M objective and the formal privacy/soundness obligations
remain open. This follow-up does not claim that general GKR certification is
impossible; it establishes that this more specialized pilot still loses.

## Implemented changes

1. `rebalance_r21_dag.py` flattens only single-use additive or product regions,
   preserving shared boundaries. Signed integer coefficients and factor
   multisets are checked exactly for every replacement. It combines shallow
   available terms first, accounting for input arrival depth rather than just
   the number of terms. There are **1627 checked local regions**.
2. `generate_r21_wiring.py` compiles each fixed layer's gate relation into a
   reduced ordered multi-terminal decision diagram. It searches deterministic
   bit/interleaving orders, interns identical subfunctions and removes equal
   branches. It independently reconstructs every represented Boolean triple,
   including skipped-coordinate subcubes, and compares the entire support and
   gate label to the original layer table. This is **exact integer/Boolean
   checking**, not a randomized rank or field check.
3. `r21_wiring.rs` evaluates that diagram directly at the three challenge
   points. Its leaves are `0`, `a+b`, `a*b`, `a-b`, `a`; an internal node is
   `(1-r)*low + r*high`. Structural zero children receive specialized kernels.
   The generic three-equality-table/full-gate scan is no longer the SBF
   endpoint evaluator. One heap buffer is reused across all layers.
4. `install_r21_structured.py` binds the generated wiring to the exact circuit
   files and ID, patches only an isolated pilot assembly, and keeps the generic
   verifier as a host-only reference. The source native calculation, source
   checks, R20 protocol, T163 and G placement remain unchanged.

| Property | Original pilot | Selected follow-up |
|---|---:|---:|
| Layers | 57 | 34 |
| Gates including copies | 6478 | 5558 |
| Copy gates | 4335 | 3415 |
| Maximum actual width | 418 | 441 |
| Certificate field values | 1926 | 1247 |
| Certificate bytes | 30,816 | 19,952 |
| Complete pilot wire bytes | 31,248 | 20,384 |

The selected wiring has **19,789 decision nodes**, maximum 1861 in a layer.
It is specialized, but not yet a logarithmic-cost evaluator for the source's
tensor/permutation structure. It still has substantial linear-size work.
The new 34-layer circuit also needs hundreds of sumcheck challenges. No
instrumented breakdown was run to assign the remaining 14.6M to individual
components; fewer nodes or layers alone is not a CU prediction.

Retained unmeasured intermediates: the original graph's decision diagram
has 20,456 nodes (`r21-wiring-b`); pairwise count-balancing produces 44 layers
(`r21-balanced-*-c`). They are not additional SBF results. The selected
depth-aware generator is candidate D; its measured assembled stage is E.

## Mathematical and source boundary

Reassociation uses commutative-ring identities with no new cryptographic
premise. For the decision diagram, exact equality on every Boolean triple
and multilinearity in each bit imply equality of the fixed wiring polynomial
over QM31. Skipped variables are valid because their two indicator weights
sum to one. The runtime tests compare arbitrary extension-field points, not
just Boolean points, and include zero and one.

These executable certificates establish the finite compiler checks described
above. They are **not a Lean theorem about Rust execution**. The original
symbolic-field/source refinement still has the same explicit open boundary:
for every canonical 24-field input, the circuit output must equal the actual
assembled ordinary/image source function. The new local transformations do
not justify silently treating the older finite source differential as that
universal theorem.

The wiring optimization alone preserves a given circuit's proof bytes and
transcript. Rebalancing changes the circuit ID and its helper certificate;
the new helper is not wire-compatible with the original 57-layer pilot.
The existing Aspis transcript and 699-field original proof are unaffected.
The helper still has no private witness or mask-seed input.

## Executed gates

- All 185 final assembled source pins reproduce byte-for-byte from the pinned
  R20 control using the checked-in stagers and generated files.
- All selected generated DAG, local certificates, circuit and wiring files
  regenerate byte-for-byte. The intermediate pairwise DAG also reproduces.
- Rust release compilation succeeds; 1088 arbitrary-full-QM31 layer endpoint
  comparisons match the independent generic wiring evaluation.
- The same 160 arbitrary source vectors, including all-zero, all-one, maximal
  limbs and arbitrary finals/images, match the native ordinary/image function.
- Both original genuine fixtures generate valid public-only helper proofs.
  Both specialized and generic host verifiers accept those same new proofs.
- Every one of 1247 certificate fields is mutated separately on each fixture;
  all reject. All 24 input bindings, output, context, circuit ID, truncation
  and trailing-byte controls reject.
- Cached v1.54 SBF compilation succeeds, without frame-overflow diagnostics.
  All 1024 source basis entries still match the frozen SBF table.
- At the diagnostic 100M cap, both helpers complete and all nine negative
  types per fixture are checked rejections. Across both caps each fixture has
  17 checked negative rejections and one late-message resource exhaustion.
  The latter is explicitly **not counted as rejection**.
- At the actual 1M cap, both honest helpers exhaust. Heap remains 262,144 bytes.
- No Lean target, axioms audit, new source witness generation, full original
  malformed regression or full original verifier replay was run unchanged.

The native cost is the retained first-pilot measurement on identical 24 field
inputs. It had the old, longer unused certificate account; it was not rebuilt
with the shorter wire merely to reproduce an already decisive comparison.
The helper numbers include its complete input/wiring checks and harness, but
not a future enclosing Aspis transcript-to-helper input binding. They remain
isolated relation costs, not full-verifier costs or savings.

## Evidence and resources

Circuit ID:
`060cd246ddf19d5798c18ec610316b1c8ee18b9227d71f53a4175dc7f04ce03d`.
ELF SHA-256:
`9f9a8e97e1e518f2313019a0e0d39767013fa0b107745d2c2f4317c8df154ce9`.
Source manifest SHA-256:
`bc5312f5237bdfceb9bbe72c5d3f4be3d39ed69ad29cd99cf383bc7a0f9bbc21`.

See [measurement receipt](evidence/r21-structured-e/receipt.json),
[world 0 raw SVM](evidence/r21-structured-e/svm-world0/svm.jsonl),
[world 1 raw SVM](evidence/r21-structured-e/svm-world1/svm.jsonl), and
[source/regeneration audit](evidence/r21-structured-integrity.json).

NUC via Tailscale; builds ran in MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128 scopes, with two release/offline/locked jobs.
SVM scopes used 2G/3G/swap0. All recorded commands exit 0 and report zero
swaps; the passing command status does not turn the failed budget into a pass.

| Target | Wall | Peak RSS KiB |
|---|---:|---:|
| Host compile | 27.24s | 544372 |
| Host source/proof gate, world 0 | 0.28s | 2464 |
| Host source/proof gate, world 1 | 0.28s | 2640 |
| SBF compile | 35.33s | 636112 |

No deployment, wallet operation, key deletion, merge or production change.
Keys generated by the SBF toolchain remain secured on the host and are not
in the evidence or Git. The user authorized pushing this research result.

## Reproduction and remaining gate

Generate the depth-balanced DAG with `rebalance_r21_dag.py`; generate its
layers with `generate_r21_layers.py`, then its wiring with
`generate_r21_wiring.py`. Assemble a fresh stage with `stage_r21_pilot.py`,
`install_r21_circuit.py`, and `install_r21_structured.py`. Run the existing
host/SBF/SVM runners in the documented capped scopes. The cheap audit is:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r21_structured.py \
  --control /path/to/pinned/r20-clean-b
```

**Decision:** retain and push this tested research improvement; reject its use
in the verifier. Generic DAG layering, even rebalanced and diagram-specialized,
has not supplied the required cheap tensor-block certificate. That would need
a different, source-bound circuit organization and a measured complete helper
below native cost before expanding the architecture. Full source refinement,
the acceptance implication, actual Fiat–Shamir/shared-oracle soundness, and
the pre-existing original privacy/retry/publication obligations remain open.
