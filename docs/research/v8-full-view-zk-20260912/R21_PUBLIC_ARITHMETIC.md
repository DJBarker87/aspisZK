# R21 ordinary-arithmetic pilot: measured and rejected

2026-09-22. The ordinary/image helper is implemented and tested, but its
complete isolated verification costs **29,796,433 / 29,793,326 CU**. The same
native arithmetic with the same public inputs costs **791,311 / 791,499 CU**.
This pilot is about **37.65 times more expensive**. Its actual 1M executions
exhaust. Following the packet's stop/go instruction, it is **not integrated
or expanded** to semantic, preparation, G or query calculations.

The complete R20 verifier is unchanged: its previously measured clean totals
remain **2,865,333 / 2,866,803 CU**, not 29.8M. No new complete Aspis run or
sub-1M result is claimed. This rejection concerns the implemented generic
layering/wiring pilot, not an impossibility theorem for specialized arithmetic
certification. The requested structure-aware wiring implementation is still
open; the generic baseline does not satisfy that optimization requirement.

Branch: `research/v8-r21-public-arithmetic-20260922`, based on
`6f00e7f6c893c3a81bc37526e32d563434d303c8`. All additions are research tools,
the immutable packet, and evidence. No production path, original transcript,
privacy profile, G selection, T163 map or negative regression was changed.
No merge, deployment, network transaction or wallet operation occurred.

## Provenance and source interface

Packet archive SHA-256:
`679fbccd8fcd5e5e97bd4fa48aedc00fa0fcbd36eca7e883e28e95126dd51763`.
All 17 manifest entries and five Git blob pins match. This packet has no
`CODEX_TASK.md`; [its README](r21-pack/README.md) and
[design assignment](r21-pack/design/PUBLIC_ARITHMETIC.md) govern the work.

The stager validates all **173** files of the actual R20 clean-B assembly,
not a generic repository field template. Its ELF hash is
`fbaaab12e5f0e798dde28626abadb61cff69354cabb2dcf3f1125559efb2db8c`.
The resulting helper and native stages each have 183 checked source pins.
Their complete flags and manifests are retained in
[pilot evidence](evidence/r21-pilot-a/pilot-receipt.json).

`r21_native::compute` wraps the actual `r19_channel_ordinary::terminal_shared`
and `r17_weighted_groups::Kernel`, with the actual basis transport. It computes

```text
dot4(ordinary(audit, abc, alpha, beta), finals)
  + (1 - beta + beta*tau^2)
      * image_terminal(tau, abc[1], abc[2], alpha) * finals[3].
```

The 24 public QM31 inputs are exactly:

| Indices | Meaning |
|---|---|
| 0..10 | Ten semantic challenges and kappa (`audit`, 11 fields) |
| 11..13 | Three chord challenges `abc` |
| 14..17 | All four relation fold challenges |
| 18 | Channel challenge beta |
| 19..22 | All four final coefficients |
| 23 | Image challenge tau |

T163, pivot/inactive corrections and arbitrary image residuals remain.
The image expression is an algebraically identical transcription of the
callback, not a byte-identical function copy. The original function hash is
recorded. G and query contributions are explicitly outside this relation.

Host-only capture immediately after the real ordinary call obtains these
inputs during acceptance of both retained genuine R19 fixtures. The helper
generator takes only these public inputs and a digest of the original
`proof-1.bin`, `public.bin`, `transition.bin` and `binding.bin`, with domain
and length framing. It has no witness or private-mask-seed argument.

The standalone SBF harness parses the 24 inputs and context from its readonly
account. It **does not authenticate their correspondence to the original
Aspis transcript**. That binding would be the enclosing verifier's job in a
future integration. Consequently even this losing measured cost excludes
such integration glue; it is not a complete accelerated Aspis cost.

## Implemented arithmetic proof

The symbolic field adapter executes the source ordinary calculation to emit
a fixed Add/Sub/Mul DAG; it does not accept prover-supplied wiring. A separate
native-field evaluator checks the generated graph. The generator prunes dead
nodes and carries live values through adjacent layers using copy gates.
Constant/CSE simplification is independent of input values.

| Fixed circuit property | Result |
|---|---:|
| Raw / reachable DAG nodes | 2239 / 2173 |
| Layers | 57 |
| Input leaves | 30 (24 public, 6 constants) |
| Maximum actual / padded width | 418 / 512 |
| Gates, including copies | 6478 |
| Copy gates | 4335 |
| Certificate field values | 1926 |
| Certificate bytes / including public header | 30,816 / 31,248 |

Circuit ID:
`a68bd47a8b72b811bd91b59c5e9ed50cf2ae21be0cbe5217a9f04741bb8b82a9`.
Regenerating from the retained source DAG yields byte-identical circuit,
profile and wiring files.

For each layer the prover performs a quadratic sumcheck over the two previous
layer indices, supplies two endpoint evaluations, then supplies a degree-k
line restriction to reduce those endpoints to one next-layer claim. The
verifier checks the actual fixed wiring polynomial and finally evaluates the
input multilinear extension from **all actual public inputs and constants**.
There is no trusted-provider or unchecked-output interface.

At a gate, the checked polynomial uses the Boolean wiring indicator times
`a+b`, `a*b`, `a-b` or `a`; summing over Boolean indices recovers the layer's
multilinear extension. Each sumcheck variable has degree at most two. The
line restriction has degree at most the previous layer's index length.
These are the algebraic construction and honest-completeness identities,
not a machine-checked source or noninteractive soundness theorem.

The verifier **scans all 6478 gates** to evaluate generic sparse wiring.
It includes all equality tables, public-input evaluation, canonical parsing,
line checks, SHA calls and sampling. Fixed tensor/permutation structure has
not been converted to a cheap structured wiring evaluator. The 57 layers and
their challenge traffic are further overhead. No isolated component CU
attribution was measured, so the total loss is not assigned solely to wiring.

The helper transcript binds a versioned circuit ID, original-instance digest,
24 canonical input fields, the claimed output and framed messages. SBF uses
the native SHA syscall; the host uses SHA-256. Its explicit sampler masks
four 31-bit limbs and rejects noncanonical P, with at most 16 attempts.
Domain separation is **not** asserted to create independent oracle answers.

## Checks actually executed

| Target | Executed result |
|---|---|
| Packet checks in fresh copy | 1024 basis inverse/dual cases, 89 pad images, 128 arbitrary QM31 pairings pass |
| Exact cycle certificate | Integer signed-operator equality, actual source ORDER equality; ranks 153 and 89 |
| Preliminary rank screens | Two M31 and two QM31 configurations: H1=540, G=601 |
| Rust toy prover/verifier | 12 circuits/cases, 468 checks pass |
| Source trace | Compiles and emits fixed 24-input DAG |
| Actual original host verifier | Both retained genuine proofs accept, independent host reference retained |
| Source graph differential | 160 arbitrary full-QM31 input vectors, including zero, one and maximal limbs; arbitrary finals/images |
| Public helper on genuine inputs | Both source-captured worlds generate and verify; both outputs equal native |
| Host message mutations | Every one of 1926 certificate fields changed independently, in each world; all reject |
| Host binding/framing controls | All 24 input positions, output, context, circuit ID, truncation and trailing bytes reject |
| SBF helper + native | Both compile with cached v1.54 toolchain, no frame-overflow diagnostics |
| SBF negative controls | Nine helper mutation kinds per world; all are checked rejections at diagnostic cap |
| Lean / axioms audit | **Not run; no Lean file changed and no formal theorem claimed** |

The 160-vector differential is the same test set in each fixture run, not 320
independent source tests. Two original fixtures are not a universal resource
profile; no additional original-witness fixtures were generated after this
pilot decisively failed its cost gate. Original malformed suites were not
rerun unchanged; dedicated helper parsing/mutation controls were added.

## Complete isolated SBF measurements

Totals are SVM `meta.compute_units_consumed`, including the wrapper. Both
modes use the same 31,248-byte account input and 262,144-byte supported heap.
The native mode recomputes the result and compares it, ignoring the unused
certificate. The helper mode verifies the entire certificate. These are
ordinary/image-only executions, not full original verifier executions.

| Mode | World 0 CU | World 1 CU | Actual 1M cap |
|---|---:|---:|---|
| Native ordinary + image | 791,311 | 791,499 | Both accept |
| Generic layered helper | 29,796,433 | 29,793,326 | Both exhaust |

Each helper world has 18 negative runs across the two caps: 17 checked
rejections and one resource exhaustion (late-message mutation at 1M).
That exhaustion is **not counted as rejection**. Native wrong-output controls
reject at both caps. Raw error/log classifications are preserved.

Helper ELF: `b7ffc39d4bfd419871815c3768881ec775b6a7540448a14c7f663f7888d99952`.
Native ELF: `21eb3ec0574c1b281635a1fdcce6642a0b05cfb68b6654d9a4a27cc143a6d27a`.
See [receipt](evidence/r21-pilot-a/pilot-receipt.json),
[helper world 0](evidence/r21-pilot-a/helper/svm-world0/svm.jsonl), and
[native world 0](evidence/r21-pilot-a/native/svm-world0/svm.jsonl).

## Stop boundary and first remaining propositions

**Engineering stop:** this generic pilot is rejected. Do not compose more
arithmetic into it or substitute its outputs in an acceptance path. A next
certificate attempt needs a materially shallower/structured circuit and a
fixed structured wiring evaluator, including the actual tensor/permutation
corrections, followed by another complete native-versus-helper measurement.
This packet has not established that such an implementation can meet 300k
or make the complete verifier fit under 1M.

**First universal source proposition, still open:** for every canonical
24-field input, the generated fixed circuit's output equals the actual
assembled ordinary-plus-image source function, retaining every correction.
The finite differentials and symbolic extraction are evidence, not a proof
of this universal refinement. After that, a future integrated split must
source-prove that correct certified hints imply acceptance by the unchanged
original verifier, with all inputs bound to the native transcript.

**Separate security obligations:** the actual helper Fiat–Shamir/shared-oracle
soundness theorem, sampler abort law and adaptive-query accounting are open.
The old R19 extraction/soundness and full-view privacy obligations also remain
open. Public-only helper generation supports a conditional post-processing
argument; it does not finish the original simulator, retry or publication
proof. No new hiding assumption was introduced.

**Separate short-cycle boundary:** packet replay confirms rank-89 correction
for its proposed map, but this is only an arithmetic/model result. No new
profile was installed, no genuine source 626-equation C1/H1/G/channel-message
gate was run for it, and no CU saving is claimed. Its mandatory profile and
full source-view gates remain before use.

## Resources and reproduction

All large jobs ran on the NUC over Tailscale in capped systemd scopes.
Builds used MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128 and two
release/offline/locked compiler jobs; SVM/packet scopes used 2G/3G/swap0.
No observed job approached the review threshold. Reported swaps were zero.

| Target | Exit | Wall | Peak RSS KiB |
|---|---:|---:|---:|
| Packet rank/control replay | 0 | 35.63s | 174404 |
| Toy build/run | 0 | 24.84s | 544132 |
| Corrected trace build/run | 0 | 24.56s | 543388 |
| Source host audit compilation | 0 | 12.38s | 350884 |
| Pilot host compilation | 0 | 27.43s | 542120 |
| Pilot host world 0 | 0 | 0.56s | 2288 |
| Pilot host world 1 | 0 | 0.59s | 2464 |
| Helper SBF compilation | 0 | 34.67s | 635264 |
| Native SBF compilation | 0 | 54.65s | 636164 |

Source revisions, hashes, commands, flags, wall/RSS/swap/exit records reside
in `evidence/r21-*`. The initial trace compilation's slice/array mismatch
(exit 101) is preserved alongside the corrected run, not hidden. Generated
SBF key files stay on the build host with their restrictive permissions;
they were not copied to Git or deleted.

Reproduce in fresh staging directories using `stage_r21_pilot.py` on R20
clean B, `generate_r21_layers.py` on the source DAG, then
`install_r21_circuit.py` (with `--native` for the control). Use
`run_r21_pilot.py`, `build_r21_sbf.py`, and `run_r21_svm.py` only inside the
documented bounded scopes. `collect_r21_pilot.py` retains public evidence and
enforces result classification. The cheap final integrity check is:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r21_evidence.py
```

An exit-zero integrity audit means the failed experiment is reproducibly
recorded; it does **not** mean its performance or security gate passed.
