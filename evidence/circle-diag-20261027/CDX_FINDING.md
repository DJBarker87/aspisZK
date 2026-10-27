# Circle diagnostic — 27 October 2026

Target: **`AspisR1.RPx_Deployed.deployed`**, frozen3, narrowed D188 trace fidelity. This is a diagnostic of the reported worker-kit finding. No adopted proof, shipped source, premise, trust item, game, metric, or release artifact is changed. The deployed 100-bit target is not established by this diagnostic.

## Q1 — Adopted model

**Neither `XRk_CircleModel`, `XRn_Join_CircleModel`, `XRk_qpow`, `XRn_Join_qpow`, nor the LPo copy is in the adopted closure.** The recorded reachable-constant list contains no `XRk`, `XRn_Join`, or `qpow` name. `CDX_L004` also imports the actual adopted top and checks its environment for XRk/XRn imported modules: none. This is stronger than inspecting a worker's import list.

The evidence chain is `RPv_plan.json`'s `FJv_Deployed` planned closure and `RPv_frontier.json`, followed by `RPx_import-closure-check.json`: 7,040 historical contexts plus retained `RPz7_PhaseIso`, all reached in the actual 12,712-module root header traversal. The exact root constant list is `RPx_reachable-constants.json`. `CDX_stage1.json` hashes these inputs. `CDX_L004` independently reports the declaration owners and kernel definitions for the operational helpers (42 records in `CDX_owners.json`). This was a focused audit, not a manifest replay.

The actual route is:

1. `AspisR1CircleSampleWrapper.sampler.circle_sample` in `RPz7_AspisR1CircleSampleWrapper_Funs` samples a QM31 parameter, calls the **unqualified** adapter `circle.secure_ood_circle_point_from_parameter`, then runs `unwrap_or_else` with the captured row.
2. That adapter, in `RPz7_AspisR1CircleSampleWrapper_FunsExternal`, maps records to `AspisR72Sampler.circle.secure_ood_circle_point_from_parameter`. Its fallback adapter is the **unqualified** `transcript.circle_fallback_point` in that same module. The global names matter: looking only for names under the wrapper namespace misses them.
3. The fallback adapter calls `AspisR1CircleFallback.transcript.circle_fallback_point`, which selects `[u,1+u][sample % 2]`, invokes the fallback owner's R72 mapper adapter, and returns its point. Its defensive `.Err` arm returns `(ONE,ZERO)`.
4. R72 uses `QM31.try_inv` → complex norm → `CM31.inv`/`CM31.inv_with` → base norm → `M31.inv`. The base inverse is the explicit addition chain with squaring counts 2,4,8,8,4 and final multiplications. There is **no predecessor-indexed qpow** here.
5. The mathematical sampler is `R0P.SemSource.circleSample0/1`, with `circleSampleParameterWith`, `circleFallback0/1`, the rational `SamplerCirclePolicy.point`, and `CircleChord.px/py`. These use the mathematical field inverse and ordinary power. The operational/model coordinate association is `R4TransportCircleCoordinates.circle_total_coordinates`.

`CDX_declarations.json` gives every selected operational circle/inverse/pow declaration, its actual owner module, source file, and full SHA256; the grouped inventory below reproduces it. It also includes the reached mathematical circle definitions. Generic Lean/Mathlib field operations are ordinary field operations, not another protocol qpow implementation. The other protocol-specific inverse owners and the independent `FIo_Native…QM31.pow` are included to avoid silently excluding inverse/pow declarations reached through arithmetic proofs and non-circle consumers.

## Q2 — Correctness and the two native rows

**The adopted R72 circle arithmetic uses the correct inverse.** Fresh `CDX_L002` proves, on canonical base two, base-field inversion, complex inversion, quartic `try_inv`, and quartic square = four. It also proves inverse cancellation and the zero-input `try_inv = ok none` law. All six top theorems print only `[propext, Classical.choice, Quot.sound]`. The proof applies the existing symbolic field laws; it does not normalize the full inverse exponent. `CDX_L001`'s numeral-tactic failures and resulting `sorryAx` diagnostics are rejected, retained, and superseded by L002; they are not accepted evidence.

The correctness coverage of the reached helpers is:

| Reached helper(s) | Exact justification / scope |
|---|---|
| R72 `M31.inv`; `square_n` / loop / body | `SamplerClosureCircleScalarTransport.inv_eq`, `square_eq`, `loop_eq`, `body_eq`, `inv_encode`; source transport to the proved addition-chain execution. Fresh canonical inverse-two check: L002. `square_n x n` means **n repeated squarings**, hence exponent `2^n`, not `x^n`. |
| R72 `CM31.inv_with`, `CM31.inv` | Norm construction; `SamplerClosureCircleFieldExecution.cm_inv`. `inv_with` accepts a callback: its correctness requires the callback's inverse law. The actual `CM31.inv` installs the proved `M31.inv`. Fresh canonical check: L002. |
| R72 `QM31.try_inv` | `try_inverse_nonzero`, `try_inverse_zero`; fresh L002 canonical and zero checks. |
| R72 regular/OOD circle mappers | `SamplerClosureCircleSourceExecution.source_execution`: canonical input returns exactly `encodeResult (pureMap (decode input))`, including singular-before-subfield error order. No independent correct-inverse premise is introduced. |
| Fallback owner's mapper and wrapper's global mapper | Explicit nested-record maps to/from that R72 implementation. `secure_parameter0_output`, `secure_parameter1_output`, `secure_circle_eq_r72` prove the relevant associations. |
| Both fallback functions; wrapper `circle_sample` and captured-row closure | `fallback_zero_output` / `fallback_one_output`, `firstFallbackActual` / `secondFallbackActual`; `circle_sample_total_on_circle` and `circle_total_coordinates`. Both rows are handled, including the error path. |
| `V7Tag73CurrentHelpersOpaque…M31.inv`, squaring loop | `GeneratedInverseLoop.square_n_exec`, `inv_correct`, `InverseChain.chain_pow` and `wordChain_inverse`. Symbolic range induction and chain exponent `2147483645`. |
| `AspisR64Field…inv`, squaring loop | `GuardedInverseExecution.body_eq/loop_eq/square_eq/inv_eq/inverse_correct` transports that execution. |
| `AspisR65Field…inv`, squaring loop | `ComplexBaseExecution.body_eq/loop_eq/square_eq/inv_eq/inv_encode` transports R64. |
| `AspisR66Field…inv`, squaring loop | `QuarticBaseExecution.body_eq/loop_eq/square_eq/inv_eq/inv_encode` transports R65. R72 scalar transport consumes it. |
| `AspisR1M31Inverse…inv`, squaring loop | Higher-order multiplier parameter; `SAQ_InverseSourceModel.inv_total_power`, `SAQ_InverseFieldModel.current_inv_total_inverse` instantiate the actual multiplier. The loop law is `SAQ_SquareSourceModel.square_loop_total_model`. No correctness claim for an arbitrary unconstrained multiplier. |
| `FIo_Native…QM31.pow`, loop, body | Separate translated **u64** exponentiation-by-squaring: tests the current exponent's low bit, multiplies the accumulator, squares the base, then shifts the current exponent. It has no predecessor-binder defect and is not the circle inverse. A fresh exponent-two probe was drafted but **not compiled** after the host failure below. No fresh kernel coverage of that probe is claimed. |

The generic theorem statements are copied exactly, with source hashes, in `CDX_statements.md`; their historical compiled proofs are reused. Only the six R72 diagnostic top theorems were freshly checked here. This does not claim a new universal arithmetic or source-to-ELF refinement theorem.

**Fallback comparison with R002 (reused, zero new Rust runs):**

| Row | Adopted / native x limbs | Adopted / native y limbs |
|---|---|---|
| First | 429496729, 1288490188, 0, 0 | 0, 0, 429496730, 1288490188 |
| Second | 1420643028, 1949254387, 1123299138, 892031669 | 627725989, 561649569, 396458520, 693802409 |

The adopted Result is **outer `.ok point`** for both rows, not `.fail`, `.div`, or the defensive `(ONE,ZERO)`. The retained fallback theorems give `.ok (fromR72Point (encodePoint (point parameter)))`. `CDX_compare.py` checks the literal R002 canonical limbs using only four-limb products:
`x*(1+t²)=1-t²`, `y*(1+t²)=2*t`, and a nonzero denominator. Both rows pass. Thus they give the same rational point as the adopted model. This is a tiny arithmetic fixture combined with the retained general kernel theorem, **not** a fresh Lean normalization of the two numeric outputs. `CDX_native-comparison.json` records the check and hashes R002 stdout.

R002's literal defective-worker counterpart disagrees on both rows; that remains a valid diagnostic of that counterpart. The current field, circle, transcript, sampler, and Cargo.lock bytes were also checked byte-identical to that frozen revision (`CDX_release-source-pins.json`). R002 is a retained standalone optimized rustc run, not a Cargo run: no new dependency graph/lock action is claimed. Its receipt pins frozen revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, field/circle/probe sources, rustc 1.94.1, opt-level 3, exit 0, wall 0.417370382 s, peak RSS 135360 KiB, swap 0. Its native field bodies are unchanged; the standalone copy only repairs the child-module path attribute. See `LPo_CIRCLE_PROVENANCE.json` and R002's receipt/stdout.

**Validation limitation:** the requested fresh per-definition probes beyond R72, the FIo exponent-two probe, and the new numeric fallback Lean draft were not run after the host admission/collection failures. `CDX_Fallback.lean` and `CDX_Pow.lean` are explicitly **UNCHECKED drafts**, with no accepted axiom audit. Retained generic correctness proofs and the compile-free comparison are the evidence used above. Completion of that fresh-test portion of Q2 remains blocked; this is not concealed as a passing compile.

## Q3 — Reachability and what the soundness proofs use

**The sampler fallback is reachable in both the adopted model and frozen code.** It is selected exactly when the sampled parameter has `c1 = 0` (lies in CM31). Within that set, `t = ±i` produces `SingularParameter`; other parameters produce `ParameterInCm31Subfield`. Outside CM31, `outside_has_denominator` proves the denominator nonzero and the secure map succeeds.

Concretely, let `r` be the 256-bit little-endian rank of the 32-byte block, `P=2147483647`. The sampled parameter consists of the low four base-P digits of r. The fallback condition is therefore **`r mod P^4 < P^2`**. In particular the all-zero block samples zero, reaches the subfield error, and chooses the first or second fallback according to the captured row. The earlier LPa_K018 native zero-block reachability receipt is reused; no new native reachability run occurred here. This is an actual input class, not an assertion that an adversary can force a chosen oracle block for free.

Do not confuse that reachable path with the **inner defensive error arm of `circle_fallback_point` itself**. Its two fixed parameters have `c1=1`, so the retained `secure_parameter0_output` / `secure_parameter1_output` and `fallback_zero_output` / `fallback_one_output` prove that arm is not taken for the two rows. The executable source selects modulo 2 for any usize index.

The soundness model does **not** assume that fallback never happens:

- `circleSampleParameterWith_rejected (f) (t) (ht : t.im = 0) : circleSampleParameterWith f t = f` explicitly returns the fallback.
- `circleSampleParameterWith_accepted … (ht : t.im ≠ 0)` returns the embedded rational point.
- `firstFallbackActual` / `secondFallbackActual` require the actual sampler `.ok q` and actual mapper `.ok (.Err err)` and derive the row's exact fallback output. They do not turn the error premise into unreachability.
- `circle_sample_total_on_circle (block) (row) : ∃ p, sampler.circle_sample block row = .ok p ∧ R0PCirclePoint p` has no caller success or no-fallback hypothesis.
- `circle_total_coordinates (block) (row) : ∃ p, sampler.circle_sample block row = ok p ∧ coordinates p = (model block row).1` handles both accepted parameters and both fallbacks.
- `circleSample0_mass` bounds the first bad event by `(1+deltaQ)/P^4`. `circleSample1_mass (z0) (hz0 : z0 ≠ circleFallback1)` has the same bound for the second row. The latter **retains its precise exclusion hypothesis**; it is not a uniformity or no-fallback theorem. The first-row non-bad analysis supplies the corresponding exclusion where composed.

See `CDX_statements.md` for the complete copied signatures, not merely these summaries. Runtime, adaptive-oracle transport, source/body association, and ELF obligations of the headline remain exactly as adopted. Narrowed D188 does not license substituting the worker's algebraic kit for these definitions.

## Q4 — Classification

**(a) Worker-kit artefact only: the adopted circle closure uses the correct R72 addition-chain/norm inverse; use `AspisR72Sampler.field.QM31.try_inv` with `SamplerClosureCircleFieldExecution.try_inverse_nonzero/zero`, or the adopted `AspisR1CircleFallback.transcript.circle_fallback_point` and `RawCircleFallbackOutputBridge`, through explicit carrier maps—not XRk/XRn qpow—for the circle leaf.**

This classifies the reported predecessor-recursion finding. It removes no premise, repairs no adopted proof, and does not certify unrelated missing source-refinement obligations. Fresh-test coverage remains limited as stated in Q2.

## Receipts, resource policy, and stopping point

| Attempt / target | Exit | Wall s | Peak RSS KiB | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| L001 / CDX_Arithmetic | 1 | 3.511594291 | 3783836 | 0 | rejected numeral-tactic failures; sorryAx diagnostics excluded |
| L002 / CDX_Arithmetic | 0 | 2.139371516 | 3812576 | 0 | six reports, standard three only |
| L003 / closure preflight | no compiler | — | — | — | N/A; job LEAN_PATH omitted toolchain `Lean` |
| L004 / CDX_Closure | 0 | 2.739290481 | 5796384 | 0 | N/A; metadata audit declares no theorem |
| L005 / fallback admission | no compiler | — | — | — | N/A; no reservation/config/receipt created |

Actual compiles: **3/40 Lean; 0/5 new Rust; 0 Kani**. Five launch IDs were allocated conservatively. All compiles use source revision `18fb80cd5a1ad87c7e9f0b2f6cf553c84c5c0067` with exact dirty source snapshots/hashes in each receipt. Every compiled receipt pins the Aeneas library objects selected by its LEAN_PATH. L001/L002 use the coherent SInt2 workspace; L004 uses the already replayed adopted cohort to audit its actual owners. No missing dependency was rebuilt, no shared object was overwritten, and no full regression was rerun.

One scope at a time; `lake env lean -j1 -M7000 -DElab.async=false`; MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64. Each admission preceding a scope had exit 0 **and** `allowed:true`. No timeout, memory kill, or cap increase occurred. L003 is a job search-path error fixed without modifying the unchanged launcher; L004 then passed. The L003 planned configuration's old SInt2 library inventory was not a compiler receipt and is not used as replay-library evidence; L004 pins the actual replay selections.

**Host blocker (local-lean rule 5):** L005 could not collect its reservation log (`scp: …CDX_L005-barrier-0.log: No such file or directory`; an independent SSH reported `Connection closed by 100.108.41.90 port 22`). The single permitted missing-receipt retry also failed with `scp: Connection closed`. No admission was inferred and no dependent proof launched. New host launches stopped; launcher/admission infrastructure was not repaired. Subsequent cleanup confirmed that L005 had no config, reservation, or receipt, and removed only this job's compiled-object scratch (`CDX_cleanup.log`). The lead must restore reliable admission/collection before the remaining fresh Q2 probes can run.

No shipped/cfg(kani) file changed, so the conditional ELF rebuild trigger did not fire. Inherited, **not rebuilt** pins: default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`; devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`; Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`. No session A worktree/candidate edit, key action, push, merge, binary, or object commit. Assumptions discharged/added/changed: **none**.

## Q1 declaration inventory

Operational entries are kernel-owned declarations reported by L004; mathematical entries are matched to the unchanged replay source selection and RPx reachable constants. Each group has one source file and SHA256; every declaration in that group shares those pins.

### `AspisR1CircleFallback.FunsExternal`

File: `evidence/replay-dry5-20261026/RPz4_FallbackExternal.lean`
SHA256: `3c30d02722125b22d8ae6917d59e2b24eea7cf450f177d82e599a25ed6046128`

- `AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter`

### `AspisR1CircleFallback.Funs`

File: `evidence/replay-dry5-20261026/RPz4_FallbackFuns.lean`
SHA256: `9e5e4a091642ab8a0f788f89fef65b0b64e940dc67d2d58c76be3c683d036bc9`

- `AspisR1CircleFallback.transcript.CIRCLE_FALLBACK_PARAMETERS`
- `AspisR1CircleFallback.transcript.CIRCLE_FALLBACK_PARAMETERS.eq_1`
- `AspisR1CircleFallback.transcript.circle_fallback_point`

### `RPz7_AspisR1CircleSampleWrapper_Funs`

File: `evidence/replay-dry8-20261026/RPz7_AspisR1CircleSampleWrapper_Funs.lean`
SHA256: `3274a84163d4b3aa76739ce8e036f6faf61229c91090902970deb320a748d0cd`

- `AspisR1CircleSampleWrapper.sampler.circle_sample`
- `AspisR1CircleSampleWrapper.sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint`
- `AspisR1CircleSampleWrapper.sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once`

### `SAQ_InverseExplicitMul`

File: `lean/SAQ_InverseExplicitMul.lean`
SHA256: `7b672677e79c3ca2c99c6d24c785a402dbb32e91595b034bb621a80ab0a378be`

- `AspisR1M31Inverse.field.M31.inv`
- `AspisR1M31Inverse.field.square_n`
- `AspisR1M31Inverse.field.square_n_loop`
- `AspisR1M31Inverse.field.square_n_loop.body`

### `AspisV8R19.GuardedFieldSlice`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedFieldSlice.lean`
SHA256: `061f207323ab0988b9a6a7936978a31c31545ab6c4fc26cf3b1518d4708da614`

- `AspisR64Field.field.M31.inv`
- `AspisR64Field.field.square_n`
- `AspisR64Field.field.square_n_loop`
- `AspisR64Field.field.square_n_loop.body`

### `AspisV8R19.ComplexFieldSlice`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ComplexFieldSlice.lean`
SHA256: `7e8c934965ea57617e493ab9ef35ea5dad02f1e952ed59e69aab2a2b7646370d`

- `AspisR65Field.field.M31.inv`
- `AspisR65Field.field.square_n`
- `AspisR65Field.field.square_n_loop`
- `AspisR65Field.field.square_n_loop.body`

### `AspisV8R19.QuarticFieldSlice`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/QuarticFieldSlice.lean`
SHA256: `73917c7a8d725f9a92a2e1b5d674f7790606159e9be992e73de55e895c2578f8`

- `AspisR66Field.field.M31.inv`
- `AspisR66Field.field.square_n`
- `AspisR66Field.field.square_n_loop`
- `AspisR66Field.field.square_n_loop.body`

### `AspisR72Sampler.Funs`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisR72Sampler/Funs.lean`
SHA256: `b693c4bc5c00835a3f0fe3ff2b895ce58f40c6a52cf6cfdfdac7beacde8e000e`

- `AspisR72Sampler.circle.secure_circle_point_from_parameter`
- `AspisR72Sampler.circle.secure_ood_circle_point_from_parameter`
- `AspisR72Sampler.field.CM31.inv`
- `AspisR72Sampler.field.CM31.inv_with`
- `AspisR72Sampler.field.M31.inv`
- `AspisR72Sampler.field.QM31.try_inv`
- `AspisR72Sampler.field.square_n`
- `AspisR72Sampler.field.square_n_loop`
- `AspisR72Sampler.field.square_n_loop.body`

### `RPz7_FIo_NativeFuns`

File: `evidence/replay-dry8-20261026/RPz7_FIo_NativeFuns.lean`
SHA256: `44783123aa6f4e7e1e0c492b25c5c41e695794ec170fde8f12925fc21deee7c8`

- `FIo_Native.aspis_core.field.QM31.pow`
- `FIo_Native.aspis_core.field.QM31.pow_loop`
- `FIo_Native.aspis_core.field.QM31.pow_loop.body`

### `AspisV8R19.InverseFieldSlice`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/InverseFieldSlice.lean`
SHA256: `18966adb21e1c93ffa007e72e6292553c2ad654049ba457554190539eb452600`

- `V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv`
- `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n`
- `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop`
- `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop.body`

### `RPz7_AspisR1CircleSampleWrapper_FunsExternal`

File: `evidence/replay-dry8-20261026/RPz7_AspisR1CircleSampleWrapper_FunsExternal.lean`
SHA256: `333c99752d98b2b195203bddbb781549c8bd4114d6dc271f8897378230a38374`

- `circle.secure_ood_circle_point_from_parameter`
- `sampler.circle_sample.closure`
- `transcript.circle_fallback_point`

### `R0P.CircleSampler`

File: `docs/research/100bit-spend-path-20261013/evidence/lean-literal-circle-density-20261015/import-sources/R0P/CircleSampler.lean`
SHA256: `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100`

- `R0P.SemSource.circleFallbackParameter0`
- `R0P.SemSource.circleFallbackParameter1`
- `R0P.SemSource.circleFallback0`
- `R0P.SemSource.circleFallback1`
- `R0P.SemSource.circleSampleParameterWith`
- `R0P.SemSource.circleSampleParameter0`
- `R0P.SemSource.circleSampleParameter1`
- `R0P.SemSource.circleSample0`
- `R0P.SemSource.circleSample1`

### `R0P.SemD2`

File: `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean`
SHA256: `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0`

- `R0P.SemSource.qm31Sample`
- `R0P.SemSource.qm31Rank`

### `AspisV8R19.SamplerCirclePolicy`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SamplerCirclePolicy.lean`
SHA256: `2aeaf83e87e04f4cd9cda722a5c0f9e8ae0f85f24e12e2edb359cdee7cf73f7b`

- `AspisV8R19.SamplerCirclePolicy.point`
- `AspisV8R19.SamplerCirclePolicy.pureMap`

### `AspisV8R15.CircleChord`

File: `docs/research/v8-full-view-zk-20260912/lean/AspisV8R15/CircleChord.lean`
SHA256: `395b20e9b1bdc85d82b23d09ec0d796a3817e553c7472c751575e7d11c266a95`

- `AspisV8R15.CircleChord.px`
- `AspisV8R15.CircleChord.py`
