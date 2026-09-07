# Joint image/relation review: restricted causal theorem proved

2026-09-07. Research parent `67ba3ff1377bbb788d33e2e4a30b5b8b9bf1f5e9`.
Separate V8 source `07b66afc22288a6ff460180242b73de4f341e02d`, inspected
read-only and unchanged. Main advanced independently to
`e0f02bc3c6dd1ee76407e55cba7bfebc23279223`; its dirty semantic/closure files
were preserved. The cached V5 import source and olean remained identical.

## Conclusion

The supplied joint bound survives review. A new Lean development proves its
**causal discrepancy-game version**, including adaptive final selection and
all four sequential relation rounds:

    acceptance <= (q+2)/|G| + 24/|A| + choose(d,q)/choose(|D|,q).

For ideal whole-field A, nonzero-field G, d=255, q=22 and |D|=262144,
the exact rational is **2^-118.4150374966**, strictly below 2^-118.
This is a rejection bound for **exact polynomial virtual quotients with an
invalid image**, not a global V8 security level. No successful recovery,
candidate membership, or assumed acceptance-probability cap appears in the
game's data. Exact source/encoder bridges remain explicit obligations.

The pinned V8 implementation does **not** install the image gate. Its source
contains OOD and query kernels and an isolated CU probe, not a complete V8
relation verifier. This continuation adds a research-only model/prototype;
it does not claim a proof-only repair of an existing accepting V8 path.

No candidate has yet met the whole 100-bit, full-view-ZK, CU-parity contract.
The q22 body model remains 40,282 bytes, exactly the user's allowance and
282 bytes above 40,000. It fits 40 KiB separately, with 678 bytes spare there;
that spare space is not additional user-authorised budget.

## 1. ZIP audit and actual source map

`aspis_v8_joint_image_review.zip` SHA256:
`644df6b343daaed48f1819b1f98a968bcffd69d642507b7b2353858fc42eff39`.
Five entries, 30,774 uncompressed bytes, no path traversal. All text and code
were read before execution. The four supplied SHA256 checks pass; the exact
package is vendored under `experiments/joint-image-package/`. Its executable
output reproduces the supplied JSON. No third-party upload was used.

| Source at the pinned revision | What actually exists |
|---|---|
| V8 `v8_deep.rs:109` | zeta0, vector0 absorption, distinct zeta1, vector1 absorption; continuation before gamma |
| V8 `v8_deep.rs:160` | Nonzero gamma sampler, caller responsible for preceding work record |
| V8 `v8_deep.rs:309,603,659` | Chord quotient reference and optimized query kernels |
| V8 `v8_a100.rs:123` | Direct bounded q22 schedule, no selectable compact-frontier counter |
| V8 `programs/aspis-verifier/src/v8_deep_cu_probe.rs` | Parse/kernel modes, fixed gamma fixture, checksum; no relation terminal, authentication, settlement or image gate |
| Parent `v6_transcript.rs:547` | Compact relation c4 reconstructed as claim/4-c0, six transmitted coefficients |
| Parent `v6_transcript.rs:762,858` | Response absorption before alpha0 and each later alpha; final256 after alpha0, queries then nonzero rho |
| Parent `v6_transcript.rs:830` | Shifted Tag-73 query injection, preserving the prior constant term |
| Parent `Pool/V7RelationCandidateBinding.lean` | Candidate/weight convolutions, exact boundaries and later-repair implications; not a V8 image-aware execution |
| Parent `relation-link.md` | Proposed E1/E2 image constraints and transpose, not installed acceptance |

Search covered both V8 modules, their Rust callers, the verifier probe and
pool dispatch. No E1/E2 or tau gate was found. Prover rank-probe filenames
containing “image containment” concern hiding linear algebra, not this gate.

## 2. Proposed transcript addition and implementation obligations

All semantic/C1/C2 data, both OOD vectors, gamma, chord and ordinary relation
weights/scalar must determine Q,w,C **before** tau. Ordinary claims must not
be selectable after tau. Then, before requesting the first six relation
coefficients:

    absorb(PROFILE, b"aspis-v8-image-gate-v1")
    tau = challenge_nonzero_qm31()  // exhaustion rejects
    w += tau*e1023 + tau^2*(b*e1022 - c*e1021)
    C unchanged
    response0; alpha0; final256; queries; rho; response1; alpha1;
    response2; alpha2; response3; alpha3; terminal dot

The first two lines are an explicitly **proposed research framing** using
the existing transcript API, not a registered production profile or a final
protocol selection. `image_gate.rs::derive_image_tau` type-checks against the
pinned transcript source; it is not exercised with a hash backend by the
ideal-input tests. The caller-prefix obligations are documented, not silently
enforced by that helper. `Frozen::mix` installs the image weights before the
prototype obtains a response. Its full q vector is a reference-model object,
not something the real verifier can read without authentication.

Normal challenge derivation adds three hash calls: a 56-byte framed absorb
(two SHA-256 compression blocks), a 33-byte squeeze and 33-byte advance
(one block each). A conservative bounded maximum is 25 hash calls: one absorb
and at most three QM31 attempts, each at most four two-hash blocks under the
existing limb retry limits. These are source operation counts, **not CU**.
No extra proof-carried tau, image claims, nonce or certificate is proposed.
The new transcript requires a distinct version/profile and a new FS/source
audit before any deployment; none was changed here.

The compact four-terminal contribution is:

    [0,0,0, alpha1*alpha2*alpha3/256 *
      (tau*alpha0 + tau^2*(b*alpha0^2-c*alpha0^3))].

The standalone expression uses 8 generic QM31 multiplications, 2 QM31
squarings and one fixed M31 scaling, before any reused powers. It needs no
live inverse. This count excludes challenge hashing, parsing and all other
verification. It is part of the carried relation, not a late membership test.
The zero-fold/nonzero-E1 kernel remains an explicit regression.

## 3. What Lean now proves, and what its definitions require

`experiments/JointImageGame.lean` is a new, focused 284-line leaf (not a
package replay). Its main theorem is `restricted_joint_bound`.

- `Rounds n c` is an inductive causal strategy. A degree-six discrepancy
  polynomial has boundary `4*(p[0]+p[4])=c`; its child strategy is an arbitrary
  function of the next challenge. After n rounds, acceptance is **defined**
  as final discrepancy zero. `rounds_false_bound` proves n*6/|A| from c!=0.
  No future response is required to be fixed before an earlier challenge.
- `AfterFold` chooses the actual difference F-F* polynomial after alpha0.
  Its degree bound is d. Its prior may be arbitrary when the difference is
  nonzero; when it is zero, the prior equals the carried true-fold discrepancy.
  The query-residual vector is zero exactly when all scheduled points agree.
  These are algebraic interface obligations, not probability assumptions.
- A nonzero difference gives at most d matching points, hence at most
  choose(d,q) passing distinct q-subsets. For equal finals, a wrong prior
  remains a nonzero constant if residuals vanish. The shifted batch is proved
  nonzero if **either** the prior or any residual is nonzero, with degree<=q.
- `ImageGame` fixes the ordinary prior and nonzero (E1,E2) before tau, lets
  response0 depend on tau and the entire `AfterFold` depend on tau/alpha0.
  Its acceptance probability is the nested exact finite average over tau,
  alpha0, queries, rho and the three adaptive relation continuations.
- `restricted_joint_bound` derives the bound from these definitions using
  root counts and finite averages. It does not take the desired bound, a
  bad-event probability, `candidateMember`, or provider success as a premise.

Ten declarations were audited: only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, new axiom or concrete QM31-universe reduction. The final replay
exited 0 in 30.30 s, 5,042,438,144-byte peak RSS, 0 swaps. See the
[axioms/time excerpt](experiments/joint-image-lean.log) and
[evidence](joint-image-evidence.json). Earlier local compile failures and fixes
are retained there; no failure was retried unchanged with more memory.

**Not yet a source theorem:** the actual natural encoder must instantiate the
exact quotient/fold and degree bounds; distinct final-domain points must be
connected; the actual scalar and query callback must provide `same_prior` and
`zero_iff`; compact response parsing/convolution must provide each boundary
and evaluated discrepancy; acceptance must imply terminal zero. The Rust
prototype checks source-shaped identities, not a universal Rust refinement.
The Lean type also deliberately contains no arbitrary-oracle decoder. Supplying
an exact polynomial quotient is the restricted class, not a recovery conclusion.

## 4. Exact ledger and byte census

| Event at its fresh challenge boundary | Bound | Applicability |
|---|---:|---|
| Nonzero image polynomial cancels at tau | 2/(k-1) | Fixed Q,w,C before nonzero tau; ideal gate only |
| Wrong first relation repaired | 6/k | Response0 after tau, before alpha0 |
| Different adaptive final evades all queries | choose(255,22)/choose(262144,22) | Final fixed before fresh distinct queries; exact true fold |
| Shifted discrepancy cancels at rho | 22/(k-1) | Arbitrary prior, residuals fixed before nonzero rho |
| Later relation repair, any of three rounds | 18/k | Sequential freshness; charged once across both final cases |

Sum before bits: **24/(k-1)+24/k+query**, k=(2^31-1)^4.
The query term alone is 221.4682257447 bits; the sum is 118.4150374966 bits.
`joint_image.py` cross-checks binomial ratios against exact product arithmetic
and 818 small parameter cases. `joint-image-results.json` records exact
numerators/denominators. Monte Carlo supplies no security certification.

Do not add 24/k again to an inventory already counting these four relation
repairs. Nor simply subtract the old 24 and declare the remaining 396430
inventory applicable to the changed V8 transcript. Global event alignment is
still required. Authentication, semantic extraction and FS resources are absent
from this local sum, not assigned zero. There is no grinding credit, unlimited
offline-search claim, quantum claim or assumed small primitive/toolchain error.

Canonical q22 body model, maximum frontier per tree 296:

    697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.

The image gate adds zero transmitted scalar values algebraically. This is a
byte-neutral *model change*, not a completed privacy/link/source wire proof.
The separate V8 kernel's packed-fixed 39,934-byte fixture is not this canonical
body. Account/instruction/upload/lifecycle overhead is not included in either
proof-body figure. No full transaction was measured here.

## 5. Executed prototypes and surviving regressions

- Supplied Python: all 2,640 image triples, 2,662 shifted-batch triples, 96
  relation discrepancies, 2,352 final pairs/23,520 schedules, four quotients,
  24 scaled image checks, 80 dense/compact weight comparisons, 15 convolution
  identities and four kernel examples passed. 2.51 s, 23,379,968-byte RSS.
- New optimized production-field Rust: 320 terminal-value comparisons, 320
  adaptive relation-round identities, 80 exact query-injection identities,
  four final-only counterexamples and twelve image-valid controls passed.
  Three tested terminal collisions occur and are correctly explained by a
  named repair; this is a probabilistic gate, not deterministic rejection for
  every alpha. Final run 0.50 s, 1,769,472-byte RSS, zero swaps.
- Changed full-degree Rust: 32 explicit natural-tensor E2=512*gamma^lane
  checks passed, including equal-x OOD pairs and semantic/mask-only lanes;
  1,280 literal fold checks retained. 0.86 s, 2,473,984-byte RSS, zero swaps.
  This rerun has a new image-residual assertion, not an unchanged regression.
- Parameter ledger: 818 exact small cases plus default q22 sum/body counts.
  0.08 s, 18,563,072-byte RSS, zero swaps.

These times/RSS are research-check workloads, **not honest prover performance**.
No full proof generation, dense rank elimination, SBF build, remote job or
full transaction execution was performed. No account or production code changed.

The original, paired and high-J root-product controls remain in
`adaptive-tail-results.json`; their unchanged heavy predecessors were not
rerun. Their zero target is image-valid but their virtual word need not be an
exact polynomial globally. They cannot be put into `ImageGame` by assumption.
In particular the high-J lower-bound subevent near 2^-107.156 remains visible;
it is neither an upper bound nor a full accepted payment forgery.

## 6. Next decision

Primary remains QM31 q22 under 40,282 bytes: this gate removes the exact-
polynomial/invalid-image obstruction at a very small algebraic cost. Fallback
remains full quintic q22 at 42,984 bytes (+2,702), an unapproved field-port
control with unresolved source/hiding/CU obligations. QM31 q23 at 41,527
bytes is still the +1,245 bounded-family control, not an accepted size increase.

The single most decisive next mathematical experiment is now a **joint
image/relation-and-query upper bound for image-valid non-polynomial adaptive
outside branches**, tested against the high-J and paired constructions. It
must construct coverage or bound accepted discarded mass, not assume the
actual word is a code polynomial. Stop that argument if it discards `none`,
requires a post-challenge target to be fixed early, or only upper-bounds a
covered branch. Passing this restricted theorem does not soften that gate.

A bounded source follow-up is separately available: integrate the sparse
image term into an isolated complete relation callback, prove the four listed
algebraic interfaces, and test T_512 with true and altered final256. Do not
start full SBF/production work before those interfaces and full-view hiding
have a viable design. CU parity still has to offset the known q22 increase
of 198 internal Merkle hashes and twelve leaf hashes across both trees.

## Commands

From the research worktree root:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/joint-image-package/check_joint_image.py
python3 docs/research/v8-no-work-100-20260907/experiments/joint_image.py
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/image_gate.rs -o /tmp/aspis-v8-image-gate
/usr/bin/time -l /tmp/aspis-v8-image-gate
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/adaptive_outside.rs -o /tmp/aspis-v8-adaptive-outside-image
/usr/bin/time -l /tmp/aspis-v8-adaptive-outside-image
```

From the cached `/Users/dominic/ZK/AspisFormal` workspace, only this leaf:

```sh
/usr/bin/time -l lake env lean /Users/dominic/ZK/.worktrees/ZK-v8-no-work-100-20260907/docs/research/v8-no-work-100-20260907/experiments/JointImageGame.lean
```
