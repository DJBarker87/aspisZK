# NUC performance prototype — four-second proving, CU failure

2026-09-08. Base research revision
`163fe7c731102f5f964be4427113863a19284c7d`; scoped source changes accompany
this report. Mathematical/security obligations are assumed for this
performance experiment, not discharged or promoted. Production is unchanged.

## Result

The genuine synthetic-transfer prototype proves in **4.034–4.060 seconds**
(three predeclared seeds, mean **4.046 s**) on the NUC's Intel Core Ultra 7
155H. Reusable compiler/encoder/interpolation-matrix setup takes **1.309 s**.
The three-proof process peaks at **207,699,968 bytes / 198.08 MiB RSS**,
with zero task swaps. These are measured samples, not a latency-tail guarantee.

The same proof bytes pass the isolated SBF research verifier under a
diagnostic budget, consuming **7,312,575 / 7,317,164 / 7,321,343 CU**.
They **all exhaust 1,400,000 CU**. This implementation plainly does not fit
the on-chain budget, even before adding pool settlement. It is not a
matched complete-transaction comparison with V7, nor a lower bound on the
best implementation of this protocol.

[Machine-readable results](performance-results.json),
[host measurements](evidence/performance-host-final.log),
[SBF measurements](evidence/performance-svm-selected.log).

## What actually runs

The producer uses the genuine transfer compiler, source masking material,
26 M31 C1 columns, adaptive QM31 H/G/D, the circle log-20 encoder,
salted commitments, the literal selected semantic round producer and
selected terminal. It then executes the two sequential component-OOD
responses, gamma, inactive claim, shifted kappa row powers, chord
transport, carried tau image check, response-before-alpha compact rounds,
final256, uniform-distinct q22 schedule, shifted rho injection and both
Merkle frontiers. All nonce slots are fixed to zero: no grinding/search.

The host and SBF verifier share `performance_verifier.rs` and the existing
research callback. The verifier starts from **proof bytes and public input
bytes**, not witness/anchor coefficients or a prover's saved transcript.
SBF uses the actual SHA256 syscall; host uses SHA256. Public context and
the 32-byte research statement binding are inputs to a three-read-only-account
probe. It does not independently authenticate that context, implement the
production statement/deployment preamble, or settle a pool transaction.
The high-budget local simulation is not a transaction that could run on-chain.

No extractor, graph capture, Gao decoding, corruption search, full-domain
chord reconstruction or repeated witness validation is timed as proving.
Public interpolation-matrix construction is explicitly timed as setup.
The producer still includes several self-checks and prover-side transcript
replay; its time is not a fully optimised production-prover benchmark.
Disk writes of synthetic public/proof artifacts occur after the proof timer.
No witness, owner secret or mask material is logged or published.

## Phases and implementation findings

Representative selected-kernel run, seed 1:

| Prover phase | Seconds |
|---|---:|
| Masking | 0.00047 |
| C1 encoding | 0.379 |
| Salt generation, C1 packing/tree | 0.759 |
| C2 helpers and encoding | 0.159 |
| C2 packing/tree | 0.369 |
| Literal semantic producer | 2.383 |
| OOD, transpose and quotient | 0.00885 |
| Relation, openings and serialization | 0.00092 |
| Total excluding reusable setup | 4.060 |

The dense committed column arrays account for
`(26*4 + 3*16)*2^20 = 159,383,552` bytes (152 MiB).
Trees, salts, encoder buffers and other live allocations are additional;
the measured RSS includes them. This is a host prototype, not a phone/browser
measurement, and not a full-view ZK result.

Representative **metered** SBF stage deltas, seed 1, including checkpoints:

| Stage | CU |
|---|---:|
| Canonical proof parsing | 35,869 |
| Public decoding, semantic transcript rounds | 174,958 |
| Selected semantic terminal | 545,547 |
| OOD transcript through gamma | 11,851 |
| Ordinary claim/chord and materialised original weights | 2,408,542 |
| Dense chord transpose | 2,290,148 |
| Public-weight/claim hashing and tau | 30,287 |
| Relation, authenticated queries, final terminal | 1,814,042 |

Entry/exit and logging overhead account for the remaining CU. These are
not all independently subtractable production costs. In particular, the
relation stage includes arithmetic as well as authentication.

Three bounded implementation steps preceded this measurement:

1. A 4,544-byte SBF frame was split at the public decode/semantic boundary.
   The retained build emits no observed overflow diagnostic; this is compiler
   evidence, not a formal stack proof.
2. The literal callback exceeded a diagnostic 20M CU before completing
   preparation. A subsequent 100M diagnostic reached original-weight
   materialisation and failed heap allocation during transpose (about 22.4M
   CU spent, not a successful total). The retained original 20M log records
   the earlier bound; the later exploratory allocation log was truncated.
3. The optional `v8_performance_fast` path shares multilinear prefix
   products (3,069 multiplications instead of 30,720 for three expanded
   components) and traverses carry edges without a fresh Vec per coefficient.
   It produces the **same complete public weight vector** and preserves its
   transcript hash. Exact controls cover 8,192 weights, 4,104 carry values,
   zero/one coordinates, plus full-vector comparisons on the real challenge
   tuples in the three generated proofs. This is differential testing, not
   a new Lean/source equivalence theorem.

The fast callback alone completes at 7.697–7.706M CU. Enabling the same
arithmetic optimisation features as the selected V7 one-transaction candidate
reduces the measured result to 7.313–7.321M. Those features are listed
explicitly in the isolated Cargo manifests; no production default changes.
The selected gamma feature does not guarantee every caller gets cheaper
code in this different compilation unit: the complete suffix is measured.

The earlier 163-multiplication structured carry contraction is **not yet
integrated here**. This prototype still materialises/transposes the weights
and hashes all 16,384 public weight bytes. Its 7.3M result must not be
represented as the cost of that fully structured implementation.

## Tests, bytes and scope

All three honest host proofs pass the shared byte-input verifier.
All three pass SBF with the diagnostic 100M cap. Altered fixed fields,
leaf payloads, Merkle frontier and truncated proof cases reject with
explicit custom errors once enough CU is available; driver assertions do
not mistake meter exhaustion for those negative-test successes.
Read-only account data is unchanged. At the ordinary 1.4M cap every honest
fixture exhausts the meter.

The public/proof artifacts generated before and after the fast/selected-kernel
changes were compared: all three proof bodies are byte-identical. Bodies
are 38,826, 39,346 and 39,814 bytes. The maximum remains

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

No additional proof claims, rounds, nonces or padding were introduced.
Public/context accounts, transaction framing, proof-account lifecycle and
pool settlement are not secretly counted as proof body or omitted from a
claimed full-transaction result: **no such result is claimed**.
Worst accepted schedules, withdrawal and all four pool transaction shapes
have not been benchmarked in this prototype.

## Reproduction and decision

All remote work was authorised on `dombarker@nuc.local`, in new directory
`/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz`.
No concurrent source/cache was overwritten. Builds used two jobs and
individual systemd scopes with zero swap, 6 or 7 GiB memory maxima; runs
used 6 GiB (host) / 4 GiB (SVM). The two concurrently running build caps
totalled at most 13 GiB on the 62 GiB machine. Cgroup sampling observed
about 1.37 GiB peak for the SVM-driver build, zero task swap.
Tools: host Rust 1.94.1, cargo-build-sbf 2.3.0 with cached platform-tools
v1.54 / Rust 1.89.0-dev, LiteSVM 0.16.0 with Agave 4.2.1 dependencies.
All dependencies were resolved offline; locks are retained. No global
rustup override, RPC, paid infrastructure, deployment or chain transaction.

On an isolated NUC source copy, with the recorded cached toolchains:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_performance_nuc.sh /absolute/new/output-directory
```

The script reuses its local targets, caps every stage, records time/RSS/swap,
and fails on SBF overflow diagnostics even if cargo exits zero.
It is syntax-checked; the equivalent individual build/run commands were
executed in this continuation. See [command/evidence manifest](performance-evidence.json).

**Decision:** local proving does not need minutes in this prototype.
On-chain fitting is not established and the measured implementation fails
decisively. The next useful experiment is an exact, carried **structured
relation-weight** implementation on the same three proof/context inputs,
with its transcript binding explicitly maintained or versioned if changed.
It must remove the measured 4.7M dense-weight cost; query inversion and the
remaining 1.8M relation/authentication stage also need measurement/optimisation.
Even deleting the dense stages does not itself establish CU parity.
Only after the verifier is competitive is a matched four-shape pool benchmark
worth claiming as the parity test. Global recovery, FS and full-view privacy
remain separate, unchanged obligations.
