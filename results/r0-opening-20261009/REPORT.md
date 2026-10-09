# R-D: authenticated R0 opening phase

Implemented on base `805f9c102` in branch `codex/r0-opening-rd-20261009`.
Executable source and KATs are committed as
`27f484a883ba0a265b0f25c947b45ea32baf1fa7`. R-B was not present on the
requested base: its available commit `f87a2d55dce94eeebbfcb14be67fdf9922453489`
was cherry-picked as `74cc03486`, resolving the `lib.rs` conflict by retaining
both exports. Its provisional row-label API remains unchanged; R-D uses its
sampler primitives with the adopted P1 encoding and labels `a0..bf`.

The reference prover commits all 29 full `2^20`-point words, constructs the
honest quotients over E, and returns a proof accepted by the `no_std + alloc`
opening verifier. The proof is **83,742 bytes**. It contains 22 fibres, 88
initial positions, 2,552 lane values, and two complete six-level eight-way
authentication paths per fibre. The full-size fixture has full-support F
messages in lanes 0–25 and full-support K messages in lanes 26–28.

The semantic phase remains a trusted integration boundary, as requested.
The fixture tests an honest opening of synthetic messages and honest 87
point claims; it does not establish that those messages satisfy the payment
semantic relation. No deployed verifier dispatch or v7 profile was changed.

## API and specification mapping

Paths below are under `aspis_core::r0`; [SPEC](../../docs/research/v8-r0-rust-20261009/SPEC.md)
and [PLAN, Decisions after S1](../../docs/research/v8-r0-rust-20261009/PLAN.md)
are the normative inputs.

| API | SPEC | Contract |
| --- | --- | --- |
| `opening::{OpeningData, Claims, Points, Endpoints, Roots}` | §6 | Compact view of the 29 committed words: two roots, two circle points, Y[29][2], three points and C[3][29]. Values and authentication live in `FibreOpening`. |
| `opening::{COPY_ACTIVE_ROW_MASKS, inactive, indicator}` | §6 | Literal fixed inactive set; 810 inactive and 214 active rows. It is never proof supplied. |
| `opening::{points_from_alphas, eq_weight, dot, powers}` | §6 | MSB-first semantic A becomes LSB-first opening points; successor uses the specified carry products; xor12 flips bits 2 and 3. |
| `OpeningData::{line, validate_points, weights, claim, interpolant_batch, claim_prime, q_weights, total_weights}` | §§5–6 | Exact secant normalization, γ^0…γ^28 batching, κ^1…κ^3 claim weights, coefficient-one inactive indicator, and τ/τ² functional rows. |
| `prover::EncodingDomain::{new, encode}` | §§3–4,7 | Full stored-domain encoder using the natural-product recurrence; generic over the existing `CodeField`, without R16 transport. |
| `prover::{Commitment, CommitmentTime}` and `Commitment::{new, root}` | §§6,9 | Separate C1 construction for lanes 0–25,D before λ/χ, and C2 construction for H1,G after them. Reject incorrect lane subfields. Retain full words and tree levels for queries. |
| `prover::quotient` | §§5,7 | Solve the exact chord linear system with e1=e2=0; inconsistent inputs return `QuotientNotInImage`, and insufficient rank returns `RankDeficient`. |
| `prover::{honest_claims, v_honest, round_polynomial, prove}` | §§6–7,9 | Honest 87 claims, inactive sum of tγ, seven polynomial coefficients with one quarter factor, six transmitted coefficients, F, and authenticated openings. `prove` checks the messages match the retained commitments. |
| `transcript::{SemanticTranscript, SemanticMessage}` | §§1–2,8–9 | P1 framing for the preserved rows 0–24, including initial C1 and row-2 C2 root binding. Enforces the row/message schedule; it does not implement semantic relations. |
| `SemanticTranscript::finish`, `SemanticBoundary::from_verified_parts` | §§6,8–9 | Explicit handoff of the verified semantic result, state after row 24, 25 challenges, two roots, and 87 claims. False semantic acceptance and non-K semantic challenges reject. The semantic caller is responsible for the provenance of this context. |
| `SemanticBoundary::{state, roots, challenges, points}` | §§6,8–9 | Exposes the handoff data; points are derived from challenges 15–24. Public statement bytes must already have been canonically encoded/validated by the semantic phase. |
| `transcript::OpeningTranscript::{z0,z1,gamma,kappa,tau,alpha,queries}` | §§1–2,9 | Exactly rows 25–31, including tagged framing and all seven reconstructed coefficients at row 30. F is absorbed before all eight Q22 squeeze/advance pairs. |
| `transcript::QuerySet::{ordered,sorted}` | §§2,8–9 | Private construction preserves 22 distinct, in-range sampler results. Ordered results preserve sampler state semantics; only opening serialization sorts them. |
| `r0_transcript::queries_from_pairs` | §2 | Small R-B adapter sharing `QueryScan`, returning scanOut's selected state after the caller computes all eight pairs. Exhaustion is an error. |
| `wire::{OpeningProof,FibreOpening,PROOF_BYTES}`; `OpeningProof::{parse,encode}` | §9 | Fixed widths/tags/lengths, canonical limbs, F/K lane widths, exactly 22 openings, and no trailing bytes or alternate query list. |
| `merkle::{Tree,Path,leaf,parent,verify_pair}` | §§8–9 | Full SHA-256, eight-way, six-level trees and fixed complete paths. See lineage and width interpretation below. |
| `verifier::{prepare,verify}` | §8 | Parse first; derive transcript and c4; authenticate each fibre before V1; then V2. Degree ≤6 follows from the seven-element reconstructed representation. Query failure and zero γ reject through the sampler boundary. |
| `verifier::{check_v1,check_v2}` | §8 | Separate algebraic diagnostics, explicitly not standalone authenticated acceptance APIs. They expose the independent rejection checks to tests. |

The hash backend uses the existing `HashFn` convention: callers supply SHA-256
(host `sha2`, or a suitable platform SHA-256 backend). The production library
still has no normal dependencies. No new panic/unwrap/expect assertion was
introduced in the opening production modules. Fallible allocations return
`Error::Allocation`; operational inversions return checked errors.

### Quotient solve and full encoder

`quotient` first applies M_512 to the even/odd natural coefficients of t−I.
It then constructs the sparse monomial-coordinate equations from §5:

```
h0[d] = a*p[d] + b*p[d-1] + c*r[d] - c*r[d-2]
h1[d] = c*p[d] + a*r[d] + b*r[d-1]
r[511] = 0
b*p[511] - c*r[510] = 0
```

Missing negative indices are zero. Sparse Gaussian elimination over E uses
highest-column pivots, beginning with the two functional equations. This
keeps the convolution system banded. Ascending back-substitution and M_512⁻¹
recover the natural message. Every solve checks the full chord-message
residual and both functionals. It does not materialize a dense 1024² E
matrix or choose an off-image decoder.

The full encoder uses `N_(2j)(x)=N_j(2x²−1)` and
`N_(2j+1)(x)=x*N_j(2x²−1)` on the exact bit-reversed nodes, followed by the
existing `phi_inverse`. Each commitment uses F or K arithmetic according to
its lanes. This avoids invoking the direct O(1024) evaluator at every one
of the roughly 30 million committed positions. The verifier continues to
use R-C's direct exact evaluators at the sampled fibres.

## Encoding and authentication decisions

The fixed wire record order is:

```
05 | len=29*32       | beforeZ1 Y0
06 | len=58*32       | Y, lane-major then endpoint
07 | len=32          | v
09 | len=6*32        | c0,c1,c2,c3,c5,c6
0a | len=256*32      | F
0b | len=22*3296     | 22 ascending fibres
```

Every record prefix is `tag:u8 || len:u32le`. Each fibre contains four
slot-major sets of 29 values (F for 0–25, K for 26–28), followed by C1's
path then C2's path. Each path contains six levels, bottom to top, each
with seven siblings in ascending child-slot order, skipping the current
slot. The six slots are the little-endian base-eight digits of the sampled
fibre index. Claims and roots come from the semantic context; the empty
row-29 unit is implicit in the wire and explicitly absorbed as tag 08,
length zero. The last opening record is never another transcript row.

Authentication reuses the eight-way node grammar and traversal from
[`tools/r101_merkle.rs`](../../docs/research/v8-full-view-zk-20260912/tools/r101_merkle.rs)
and [`tools/r102_tree.rs`](../../docs/research/v8-full-view-zk-20260912/tools/r102_tree.rs),
specialized to complete single-fibre paths in `r0::merkle`. The lineage is
[`R549Merkle8PathBinding`](../../docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R549Merkle8PathBinding.lean)
and [`R552Merkle8LeafPathBinding`](../../docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R552Merkle8LeafPathBinding.lean),
with the tagged-leaf grammar from
[`AspisV8PairedCommitment.Domains`](../../docs/research/v8-full-view-zk-20260912/lean/AspisV8PairedCommitment/Domains.lean).
R0 leaf inputs are `10 || 71 || C1_values` and `10 || f1 || C2_values`;
the fixed value payloads are 480 and 128 bytes respectively, with no salt,
as requested. Parents are `18 || eight ordered child digests`.

The historical implementation and cited Lean path type use **26-byte**
truncated SHA-256 digests. P1's roots are explicitly **32 bytes**. This
adapter uses full SHA-256 digests consistently at every level, including
both roots, and documents that change. The old width-specific theorem is
not claimed as a Rust refinement proof for this new adapter. The independent
Python oracle pins a complete six-level SHA-256 path with all sibling
positions distinct; full-size tests exercise the two actual commitment trees.

The §6–§9 passages requiring interpretation were:

| Passage quoted from SPEC | Implementation |
| --- | --- |
| §6: “The opening data `D` contains 29 initial words W” | The task's allowed compact alternative: two roots plus authenticated opened values; the prover retains all full words. |
| §7: “An explicit coefficient procedure is to solve for q_l in the message map from §5” | Sparse linear solve after the invertible M coordinate change, with the two functional constraints as explicit equations. Reject outside the image. |
| §8: “Semantic and authentication checks are abstract Boolean propositions here.” | Semantic acceptance is the explicit trusted handoff; authentication is an actual pair of SHA-256 paths checked before each V1 equality. |
| §9: “the transcript absorbs the **full reconstructed seven coefficients** `c0..c6`, even though only six were sent on the proof wire” | `prepare` computes c4 before row 30; both prover and verifier absorb seven. |
| §9: “Field typing proposal is F for lanes 0–25 and K for 26–28, embedded in E.” | Enforced at commitment construction and by narrow canonical opening parsing. Other transcript field records use E. |
| §9: “does **not** invent an R552 node/path serialization” | Fixed complete paths use the existing bottom-up child order; the explicit width/root decision is recorded above. |
| §9: “it does not check that the repeated column equals the earlier payload” | Both Y0 and Y are retained. The prover repeats honest Y0, but the verifier adds no equality guard. Row-27 Y is used algebraically. |

## Tests and timings

| Test | Evidence/result |
| --- | --- |
| `data_bit_order_masks_and_claims` | 810/214 split; all 1024 Boolean points' MSB/LSB, successor and xor12 mappings; arbitrary-E eq-weight sum and batched claim identity. Pass. |
| `quotient_sparse_system_and_round_table` | Full-support E message, both interpolation axes, exact linear-system residual, e1/e2, rejection of false endpoints, whole-message pairing, polynomial identity including α=0. Pass. |
| `p1_whole_transcript_and_merkle_kat` | Independent Python P1 rows 0–31: every challenge and returned state, points, weights digest, claimPrime, reconstructed polynomial, S, and SHA-256 path. Pass. |
| `parser_sampler_and_schedule_rejections` | Fixed sizes/tags, truncation/trailing bytes, every limb of every field/opening record, wrong lane field, invalid schedule, semantic rejection, Q22 exhaustion and block-boundary returned state. Pass. |
| `full_size_roundtrip_corruption_and_domain_identity` | 29 × 2²⁰ actual encoded values, both actual trees, honest proof/parse/verify, coefficient equality for all 29 quotients, and explicit Enc(q)·L=Enc(t)−Enc(I) at every domain point for a full-support K lane. Pass. |
| R-C / R-B regression | All six R-C tests and nine R-B tests pass. The `r0` name filter additionally selected four existing layer0 tests, also passing. |
| `--no-default-features` library check | Release check of the existing `#![no_std]` crate. Pass. |
| Independent generator `--check` | [generate_kats.py](generate_kats.py) extends the independent R-B/R-C Python oracles; reads no Rust-produced output. Pass. |

Corruption teeth in the full-size test:

| Mutation | First rejection with untouched remaining proof | Isolated named check |
| --- | --- | --- |
| One opened value | `Authentication` | Fixed-challenge V1 rejects while V2 remains true. |
| One F coefficient | `Authentication`, because S changes | Refresh genuine paths for the new S: `V1`. |
| One Y endpoint | `Authentication`, because subsequent challenges/S change | Refresh genuine paths: `V1`. |
| v | `Authentication` | Fold honest q at the new α and refresh paths, so V1 passes: `V2`. |
| Transmitted c_i | `Authentication` | Repeat for **all six** transmitted indices, folding honest q at the new α and refreshing paths: `V2`. |
| C1 root | `Authentication` | Direct root mismatch with the same semantic-state fixture. |

The tests also hold challenges fixed, change only the polynomial, and show
V1 passes while V2 rejects. This separates the predicates without weakening
the production verifier. Refreshing paths in the isolation tests uses the
retained real trees; no authentication callback is bypassed.

Final internal full-size timings, on Intel Core Ultra 7 155H (`nuc`):

| Phase | Seconds |
| --- | ---: |
| Domain, messages, two full commitments, semantic fixture and claims | 1.446946 |
| Opening prover and proof serialization | 0.862859 |
| Opening verification | 0.025921 |
| Full-domain quotient identity check | 0.480688 |
| Entire full-size gate, including corruption tests and artifact writes | 3.923912 |

All final gates used optimized release arithmetic with overflow checks,
two compiler jobs, a reused target cache, and separate systemd scopes with
MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0. At the full-size start
another 6 GiB capped job was active; total observed reservation was 12 GiB
with approximately 50 GiB available. No scope approached a review threshold.

| Recorded command | Exit | Wall s | Sampled aggregate RSS MiB | Cgroup peak MiB | Peak swap bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| [Full-size gate](full-size.json) | 0 | 4.019 | 313.898 | 282.645 | 0 |
| [Release regression](release-tests.json), 23 tests | 0 | 1.407 | 82.051 | 53.984 | 0 |
| [no_std check](no-std.json) | 0 | 2.411 | 561.332 | 464.297 | 0 |
| [KAT reproduction](kat-check.json) | 0 | 0.201 | 30.098 | 14.871 | 0 |

Resource walls include recorder overhead. The full-size gate reused compiled
code; compilation is recorded in the earlier preflight and failed artifact
capture. Sampled aggregate RSS sums processes and can count shared pages
more than once; the independent cgroup peak is also supplied.

The first full-size run passed all protocol/corruption assertions but failed
at its final evidence write: a relative `R0_EVIDENCE_DIR` was interpreted
from Cargo's crate test directory. The unchanged gate was rerun with an
absolute destination specifically to obtain the missing artifact. Both
[failure log](full-size-artifact-path-failure.log) and
[failure resource record](full-size-artifact-path-failure.json) are retained.

[validation.json](validation.json) records toolchains, environment, caps,
revision and phase expectations. [source-manifest.json](source-manifest.json)
pins 72 compiler/oracle inputs; [source-audit.json](source-audit.json) confirms
all 72 matched the Linux build workspace. [fixture.json](fixture.json) pins
roots, transcript states, S, and the hash of [honest-proof.bin](honest-proof.bin).
The latter is a test artifact, not a valid payment proof.

Reproduce at the executable revision, inside the recorded capped scope:

```sh
python3 results/r0-opening-20261009/generate_kats.py --check
cargo test --release --config profile.release.overflow-checks=true --locked --offline -p aspis-core --lib r0 -- --nocapture --test-threads=1
cargo test --release --config profile.release.overflow-checks=true --locked --offline -p aspis-core --lib r0::opening_tests::full_size_roundtrip_corruption_and_domain_identity -- --ignored --exact --nocapture --test-threads=1
cargo check --release --config profile.release.overflow-checks=true --locked --offline -p aspis-core --lib --no-default-features
```

For artifact capture set `R0_EVIDENCE_DIR` to an **absolute existing directory**;
omitting it runs the assertions without writing artifacts. `record_run.py`
records command/status/time/RSS/cgroup/swap and refuses to run outside the
specified memory cap. Exact executed commands are in each JSON record.

This is executable Rust evidence, not a Rust-to-Lean refinement or a formal
release result. `#print axioms` is not applicable; no Lean sources, manifest
replay, SBF build, stack-limit validation, CU measurement, or semantic release
gate is included. The fixed-array reference arithmetic still needs the
separate SBF/runtime work before claiming deployment suitability.
