# R41: exact QM31 lift and a proved restricted-residual degree bound

Parent `9a9b2142709edc9a7066eab68acb09cbe4690731` (R40).
Branch `research/v8-r41-qm31-residual-lift-20260929`.

**Result:** the explicit restricted residual determinant is a nonzero
polynomial over the retained exact QM31 tower, with total degree at most
**1,105**. All 34 new Lean theorems compile with standard axioms only.
The selected 13-by-13 residual map is proved surjective wherever that
determinant evaluates nonzero. The probability of that condition under
the actual source transcript is **not yet established**.

No protocol, verifier, wire format, hiding assumption or mask sampling
changed. No CU saving is claimed.

## Exact-field lift, not a substitute field

R40's certificate is over `ZMod 2147483647`. R41 reuses the retained R15
`ExactTowerBase` unchanged:

```
M31Exact = ZMod 2147483647
CM31Exact = M31Exact[i] / (i²+1)
QM31Exact = CM31Exact[u] / (u²-(2+i)).
```

Its primality, minus-one nonsquare, and norm-based `2+i` nonsquare proofs
are retained. The existing thirty-step Euler certificate is reused; there
is no new field axiom or replacement non-residue.

`ResidualFieldLift` proves that the complete `assignedMinor` and its
determinant commute with a coefficient-ring homomorphism. This includes
the root construction, normalized chord, point weights, quotient columns
and both observation channels through the existing mapping lemmas.
An injective homomorphism therefore preserves R40's nonzero specialization.

`QM31ResidualWitness.embed` is the composition of the two actual tower
algebra maps. Its left inverse is the real-real projection, so injectivity
is proved directly. The source constants are also identified exactly:

```
embed(1073741824) = 2⁻¹
embed(536870912)  = 4⁻¹.
```

The concrete base-ring multiplication identities are kernel-checked.
R40's assignment is embedded without changing any value. Its determinant
remains nonzero; the polynomial evaluation theorem then proves nonvanishing
over QM31 itself. Thus the theorem is not limited to a host M31 experiment.

The algebraic witness remains distinct from an accepted source transcript.
In particular, its parameters 2 and 3 lie in M31 and would be rejected by
the actual OOD policy. That does not invalidate an algebraic nonzero witness,
but its existence alone does not establish a sampler-support probability.

## Degree calculation tied to the explicit model

`ResidualDegree` proves symbolic bounds, without expanding the 22-step root
recurrence or enumerating the determinant. `SourceResidualDegree` instantiates
them with the actual 36-variable model. The variables are:

- 0–9: semantic point coordinates;
- 10: kappa; 11: first relation alpha;
- 12–13: rational circle parameters u,v;
- 14–35: the 22 query-root values.

| Model expression | Proved total-degree bound |
| --- | ---: |
| Successor carry at coordinate i | 9-i |
| Each statement-point coordinate i | 10-i |
| Tensor or T163 dual-code weight | 55 |
| Normalized chord entry | 2 |
| Chord-transported point weight | 57 |
| Constructed 22-root coefficient | 22 |
| Quotient-column coordinate, including alpha powers | 25 |
| Ordinary/G combined weight, including kappa powers | 60 |
| Any residual observation entry | 85 |
| Selected 13-by-13 determinant | 13×85 = 1,105 |

The tensor bound is the checked sum 10+9+...+1, not an assumption that
the successor remains multilinear in the whole semantic point. The T163
balancing subtraction is retained. Natural-basis shifts multiply only
constant carry coefficients, so they do not increase polynomial degree.
Each query root increases the constructed root polynomial's degree by at
most one. Both relation-polynomial channels retain their distinct weights
and quarter-scaled [0,3,2,1] coefficient convention.

The determinant bound uses the retained generic `minor_totalDegree`
theorem. It is conservative: row/column-specific improvements are possible,
but no stronger number is asserted. These are algebraic root-coordinate
bounds, **not** a polynomial representation of SHA or discrete query indices.

`QM31ResidualBoundary.nonzero_and_degree` combines the unconditional
algebraic conclusions. `selected_residual_surjective` explicitly retains
the premise that evaluation at the proposed assignment is nonzero. That
conditional linear-algebra theorem is not presented as a full privacy proof.

## Source chronology and the first remaining proposition

R41 verifies the unchanged R40 source manifest (195 pins) and retains six
source files for a focused chronology/sampler inspection. This inspection
is not a new runtime test or a universal source-refinement proof.

The pinned research verifier does the following:

1. `inactive_row_binding::to_gamma` absorbs the three point-claim rows,
   samples the first OOD point, absorbs its component vector, and tries up
   to three second points until one differs. It absorbs that component
   vector and the batch nonce before nonzero gamma.
2. `r17_host_relation::prepare_mode` absorbs the inactive claim before
   nonzero kappa, then binds the compact functional and incoming claim
   before the image challenge tau.
3. `channel_challenge` absorbs **both** channel polynomial coefficients
   before beta. `verify_cached` then absorbs the first relation polynomial
   and fold nonce before the first alpha.
4. `relation_callback::query_schedule` absorbs Final256 and the query nonce
   before calling `challenge_queries_without_replacement(22, 1<<18, 64)`.
   The query-batch challenge rho comes afterward.

`Transcript::squeeze_block` uses separate squeeze and advance addresses
derived from the current state. The QM31 sampler masks four limbs and
rejects the noncanonical M31 value, allowing eight draws per limb. Nonzero
sampling allows three candidates. Secure circle sampling allows three
parameters and rejects the CM31 subfield and singular denominators.
The query sampler preserves first-occurrence order, rejects duplicate
indices and returns an explicit error if 64 draws do not yield 22 indices.
The query-root map is the source circle-fibre map followed by `2*x²-1`.

These facts do **not** justify treating all 36 polynomial coordinates as
independent uniform QM31 elements. The 22 roots are derived from a restricted
262,144-index domain, with distinctness and bounded-draw conditioning. Later
addresses depend on earlier challenges and disclosed proof messages. Source
comments describing exact uniformity are not themselves proofs for the
shared-oracle experiment, including previously queried addresses.

The first remaining source-specific proposition is therefore a justified
bound for

```
Pr[determinant(actual z,kappa,alpha,u,v,query roots) = 0]
```

in the actual shared-oracle execution, with freshness/first-hit accounting,
the exact sampler support, rejections/repeated addresses, visible failure
and retry/publication conditioning. **Do not report 1,105/|QM31| from these
theorems.** Nor would a coarse single-minor zero-set bound alone establish
the required complete privacy loss: a singular selected minor need not mean
the full correction system is singular, and the simulator/posterior and
other disclosure obligations remain separate.

The retained source files include research helpers with synthetic-context
entry points. The chronology inspection concerns the shared sampler and
the actual relation-suffix functions named above, not a claim that a
synthetic helper establishes the full deployment/account preamble.

## Verification receipts

| Focused target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Generic field lift | 0 | 1.04s | 2,264,340 | 0 |
| Retained exact tower, missing cache object compiled | 0 | 2.54s | 2,592,068 | 0 |
| Concrete QM31 witness | 0 | 1.12s | 2,458,956 | 0 |
| Symbolic component-degree lemmas | 0 | 1.38s | 2,310,304 | 0 |
| Explicit entry/determinant degree | 0 | 1.23s | 2,284,436 | 0 |
| Combined boundary | 0 | 1.24s | 2,441,876 | 0 |
| Sum/max, including retained tower | 0 | 8.55s | 2,592,068 | 0 |

All 34 new theorems and the retained tower audit use only
propext/Classical.choice/Quot.sound. The final cache has 176 objects,
reusing 170 predecessors. Twenty-two evidence artifacts plus their manifest
record source hashes/revision, exact commands, resources, audits and failures.

Two small integration failures are retained: a `mapMatrix`/matrix-map
rewrite mismatch, and a degree leaf needing explicit constant-polynomial
typing plus parentheses around a finite-sum body. The proofs were corrected
without weakening their conclusions. No memory failure or raised limit
occurred. The old tower file's historical recursion setting is unchanged;
no new file adds such a setting.

Lean runs on the NUC in scopes with MemoryHigh3G, MemoryMax5G,
MemorySwapMax0 and TasksMax128, using the retained Lean 4.32 dependency
cache. The smallest changed leaf precedes its dependent bridge. There is
no new Rust/SBF build, unchanged runtime replay or cold dependency build.

Final focused workspace:
`/home/dombarker/project-offloads/aspis-r41-lean-20260929-f`.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r41_evidence.py
```

Full-source semantic refinement, H1 compatible-image coverage, source-bound
Schur assembly with its retained posterior, adaptive simulation, coherent
pre-beta extraction, seed/commitment hops and visible retry/publication losses
remain open. No negative regression was removed.

Selected CU remains **1,620,236 / 1,621,719**; both actual 1M-cap runs exhaust.
Full privacy, soundness closure and supported-budget execution are unfinished.
