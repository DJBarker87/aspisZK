# Literal quotient family cardinality

Research parent: `bc23dfeb647320c4fbf09012cd92da1a6a5fa95a`.
Borrowed V7/V5 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
This continuation changes no verifier, transcript, proof body or production code.

## Exact target

For any fixed arbitrary received quotient word R, retain the existing family

`CandidateFamily univ R 9558`.

Its members are all natural1024 coefficient vectors Q whose actual stored
initial encoder agrees with R on at least 9,558 complete four-slot fibres.
There is no image test, provider/decoder filter, global polynomiality assumption
on R, or original-component membership assumption.

The new selected endpoint constructs a mathematical `literalFamily R` and
proves both directions of membership in that existing family, plus cardinality
at most 99. The family depends on R alone. In an execution where R is fixed
before kappa/tau/alpha, so is this family; it is **not** thereby fixed before
gamma, either component OOD vector, or early semantic/copy challenges.

## Proof architecture

`QuotientFamilyCore` reuses the checked decoded-slot/interleave equivalence
from `MaskedCurveRepresentation`. Two distinct quotient coefficient vectors
differ on at least one coefficient lane. On a common complete fibre, that
lane's two final-code evaluations agree. The selected final overlap cap 255
therefore bounds the intersection of their own supports. No union factor 4
is introduced and no sampled alpha is needed.

For each finite subfamily, the existing V5/V7 Johnson theorem is applied with
coordinate count 262144, agreement floor 9558, overlap 255 and boundPlusOne 100.
Its numerical premises reduce to the small exact arithmetic certificate

```
9558^2 - 262144*255 = 24508644
100*24508644 - 262144*(9558-255) = 12138768 > 0
262144/2 <= 100*9558
```

Thus every finite subfamily has fewer than 100 members. The finite-predicate
construction then supplies a finite set with **exact** membership equivalence,
not merely an unrelated list covering some candidates. The selected adapter
uses the existing canonical inverse identities, literal natural encoder/lift
identity and final overlap theorem; none is replaced by a caller-supplied
source-correspondence equation.

## Status and scope

Both new leaves are kernel-checked on the NUC. The literal selected family
has at most 99 members, including invalid-image candidates. This completes
the cardinality implication previously stated only as a mathematical audit.

The checked exposed API is `literal_support_intersection_le_255`,
`literal_finite_subfamily_card_le_99`, `literalFamily_card_le_99`,
`mem_literalFamily` and `candidateFamily_ncard_le_99`.

A finite mathematical family is not an efficient enumerator, decoder or
resource-bounded extractor. Its members can still have invalid images or
incorrect ordinary rows; image-valid quotient membership is not recovery of
29 original component polynomials or a valid payment witness.

The cap can support a later finite union of the prechallenge image/ordinary
polynomial exceptional events. It adds **no** factor 99 to the already-proved
off-family query term. Combining represented and unrepresented events must
also charge the one actual shifted-rho batch and three later repairs only
once. That sharper probability wrapper is not proved by the cardinality
theorem itself and is left to the next game composition.

Proof body remains 40,282 bytes. No CU, proving-time, privacy, authentication,
replay-availability or Fiat–Shamir improvement is claimed. No grinding credit
is used.

## Reproduction boundary

The fresh NUC overlay is `/home/dombarker/project-offloads/aspis-masked-tail.m4IQIB`.
Its 682 original source/output entries were checked against the new research
revision and borrowed source pin before use. They are immutable hardlinks to
the prior frozen overlay; no old file or shared native package cache is edited.
The new initial manifest retains its prior manifest hash/origin and begins with
no pending outputs. Newly checked targets are added to per-run snapshots.

Use a fresh run tag and `run_quotient_family_nuc.sh`. The runner preserves the pinned source
and compiled-artifact manifest, snapshots any newly checked dependency output,
and uses one systemd scope: MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, Lean `-j1 -M9500`. This is the previously measured native
Mathlib/selected-cache import scope, not a cold dependency build or an
unchanged higher-cap retry. All prior green proof sources and runners remain
unchanged.

| Leaf | Green run | Exit | Wall | Peak RSS | Swap | Axiom audit |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| `QuotientFamilyCore` | `quotient-family-core-nuc-v2.log` | 0 | 2.96 s | 6,684,452 KiB | 0 | Four standard-only audits |
| `QuotientFamilySelected` | `quotient-family-selected-nuc-v1.log` | 0 | 3.32 s | 6,835,928 KiB | 0 | Five standard-only audits |

The core's first check found only a missing namespace open for `coefficientLane`;
that source and failed log are retained. No limit was increased, no giant
finite enumeration was reduced, and no new axiom or `sorry` was introduced.
All audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Exact SHA-256 values:

```
QuotientFamilyCore.lean
a6e3a839415cb7365e982242bd526b0735c95e9f1cd6e1632f571ff6e0d68dfd
QuotientFamilyCore.olean
3a78e164994d8ba84200fea9936eb3c41a7d00fe29b2c630f02899099a8df3e3
QuotientFamilySelected.lean
45684f2e78f66d7fe7d7672bb0a2d1a3929a02094e55f8517b769b5f76c126a8
QuotientFamilySelected.olean
3c9ec7f60e794b5faa37abd1e8012f73ec2e02b47e8a4d5d22bca11cb1ecf7a5
```

The decisive next use is to combine this fixed pre-kappa family with the
existing image/shifted-row first-discrepancy game, then attach the one shared
rho/later-repair suffix. The cap alone is not that probability theorem.

## Evidence audit

The new read-only `experiments/audit_quotient_family_evidence.py` checks this
continuation's two cap leaves, the separate `EarlyC1Family` leaf and the
reduced `MixedC1Control` execution. It does not rerun the preceding ten leaves.
`quotient-family-transfer.json` resolves each executed source, output, runner
and per-run manifest to retained hash-checked local bytes; historical failure
snapshots are preserved separately. `quotient-family-evidence.json` records
the resulting focused status. Recheck it with:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_quotient_family_evidence.py --check-recorded
```

The new initial manifest SHA-256 is
`c7c0792100c4b9f0c98d060f9c91fec1b12ea9d836c35bb309201cf0cfefb0aa`.
Its parent is `bc23dfeb`, while its prior cached-artifact origin is `b006d34f`;
those are distinct roles, not conflicting source revisions. The audit checks
341 pinned source blobs and 341 retained compiled artifacts, and separately
walks each new target's actual imported source/output closure. It inherits
the recorded source-to-olean evidence: hash equality is not a fresh compiler
reproduction. Native Lean/Mathlib/package caches remain a declared pinned
compiler/cache boundary, not a package-wide replay or machine-code proof.
