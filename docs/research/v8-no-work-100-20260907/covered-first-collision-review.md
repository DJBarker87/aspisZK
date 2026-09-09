# First-round collisions for one fixed covered reference

Status: `CoveredFirstCollision.lean` passed its focused NUC v4 check. All six
axiom audits report only `propext`, `Classical.choice` and `Quot.sound`.

Fix `Rows`, including its quotient reference, all original covectors and
claims, reconstruction, interpolant and image coefficients, before kappa.
Let the first compact response depend arbitrarily on kappa and tau, but
not on alpha. For nonempty finite challenge sets G and A, the checked
`strategy_bound` is

```
bad image(referenceQ) OR Rows.errors != 0
  => average kappa∈G, tau∈G, alpha∈A
       1[((Rows.before kappa).firstError tau response(kappa,tau))(alpha)=0]
     <= 3/|G| + 6/|A|.
```

The strategy's actual final remains unrestricted and may depend on
kappa/tau/alpha. This event concerns the first discrepancy against the
fixed reference fold. Equality with the carried prior at the actual final
requires the caller's represented-final bridge; it is not assumed here.
Likewise the lemma does not select a quotient after a challenge and then
pretend that it was fixed before the root bound.

The proof uses a disjoint case split, not an addition of image and row
ceilings:

- If either image coefficient is nonzero, the degree-two tau polynomial is
  nonzero for every kappa. Outside its roots, the actual compact boundary
  forces the first degree-six discrepancy to be nonzero. This gives
  `2/|G| + 6/|A|`, uniformly over kappa and both response dependencies.
- Otherwise the image coefficients are zero. If any ordinary row error
  is nonzero, the shifted cubic in kappa is nonzero. Outside its roots the
  image discrepancy is a nonzero constant in tau, giving
  `3/|G| + 6/|A|`. The inactive error remains the constant coefficient; no
  independent `inactiveExact` premise is restored.

The existing `FirstImageDiscrepancy.firstError_boundary` supplies the
literal compact boundary; `ShiftedRowPrefix.before_prior` supplies the
actual affine row cubic. Existing `avg_polynomial` performs fresh-challenge
averaging, including exceptional continuations. No query-last probability,
suffix bound, authentication term or numerical source-correspondence error
is introduced. A family union may charge this first-collision indicator per
fixed candidate, while a later suffix argument remains a separate single
composition.

No verifier or protocol source changes. The proof body remains 40,282 bytes,
with unchanged query profile, canonical fields and zero work-security
credit. Payment extraction, actual replay resources, full-view privacy,
Fiat–Shamir and complete-transaction CU remain separate obligations.

## Focused evidence

Research source pin: `f19673b4fe72cf74ae687a926eeae9d1e5a6a52e`.
Borrowed V7/V5 closure pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`;
Mathlib pin: `81a5d257c8e410db227a6665ed08f64fea08e997`.
The runner checked 689 source/cache artifacts before and after the green
target; unchanged native package compilation itself was not replayed.

| Run | Exit | Wall time | Peak RSS (KiB) | Swap | Result |
|---|---:|---:|---:|---:|---|
| NUC v1 | 1 | 6.79 s | 6,673,196 | 0 | Literal natural-to-rational cast mismatch, then arithmetic elaboration timeout |
| NUC v2 | 1 | 6.80 s | 6,672,664 | 0 | Four core proofs checked; final ordered-add inference timed out |
| NUC v3 | 1 | 6.35 s | 6,675,752 | 0 | Explicit budget still triggered the generic ordered-add inference timeout |
| NUC v4 | 0 | 3.11 s | 6,712,992 | 0 | All six theorem audits standard-only |

The cast was made explicit. The final pure-rational composition uses
`linarith only [bound,lower]`, avoiding inference through a generic
`add_le_add_right` application. No mathematical statement, memory cap,
heartbeat limit or recursion limit was relaxed. Exact failed source snapshots,
logs and per-run manifests are retained alongside the green log and olean.

Reproduction command, after staging the frozen target in the pinned overlay:

```sh
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-covered-family.rfQFkf/run_covered_family_nuc.sh /home/dombarker/project-offloads/aspis-covered-family.rfQFkf CoveredFirstCollision covered-first-collision-nuc-v4'
```

The runner invokes Lean 4.32.0 with `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0 and CPUQuota 200%. No laptop compile,
package-wide build or unchanged theorem replay was run for this leaf.

Frozen source SHA-256:
`793520696dfb18c001dbad3bc7ac52a256e3403b2f3fda8e2a773c02431b6888`.
Green olean SHA-256:
`3f911a3b371a897e94e3ede005a5b218f4693a2096b5812e3bea941aa5ea3f52`.
Green per-run manifest SHA-256:
`d4530de1477f342596a6017c2c218d80022b57afe42a8cf554c52f8c1eda3b63`.
