# The old curve bound as an actual off-family agreement tail

Research parent: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`.
Borrowed V7/V5 formal source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No verifier, protocol, proof-body or production code is changed.

## New implication

Fix the arbitrary received quotient R before alpha. Let F(alpha) be the
prover's actual adaptive final, and M(alpha) its full matching-fibre count.
Define the family F_a from R alone: all circle-lift quotient coefficient
vectors whose **own** full four-slot support against R has at least a fibres.
The selected final is covered when it equals the coefficient fold of some
member of this family. This is not a same-support requirement.

The old `DegreeThreeCurveDecodable` theorem returns one large coherent subset;
it does not directly state coverage of the actual selected candidate. The new
`MaskedCurveTail.tail_card_le` closes that quantifier gap. It masks a strategy's
support to empty whenever its selected candidate is already covered. If more
than C uncovered challenges still have at least t matching positions, the
curve theorem supplies a coherent subset larger than `3*T`. The old resolving
lemma supplies one selected node whose support lies within that tuple's own
joint support. Since `a≤t`, this tuple belongs to F_a and represents that node's
actual candidate, contradicting the mask.

Consequently, for the exact curve parameters,

`#{alpha : M(alpha)≥t AND actual F(alpha) is outside F_a} ≤ C(t)`.

This uses the curve-decoding theorem's actual premise, not existence of an
unrelated predecessor, an assumed family member or a postselected root bound.
There is no multiplication by the family cardinality. For later query bounds,
the selected final is fixed before the query draw: a uniform upper matching
cap is charged once, irrespective of how many family members exist.

## Status and selected-source boundary

`MaskedCurveTail.lean` is kernel-checked. Its generic inputs are the existing
code/curve theorem and `0<t`, `a≤t`; its output is the actual selected
off-family tail. It includes the exact masked-good-set identity.

`MaskedCurveRepresentation.lean` and `SelectedMaskedCurveTail.lean` are now
kernel-checked on the NUC. The selected endpoint uses actual
canonical x/y inverse tables, the four decoded slots of the same received R,
the natural coefficient interleave, and the **full** actual folded matching
set. The representation adapter proves both directions of family membership
and final identity, not a caller-supplied correspondence equation. The selected
leaf consumes the existing V7 theorem at strict threshold 9557, so t=9558 and
the existing numerator is `9,396,508,281,246` over the full-field alpha law.
`actual_tail_card_le` proves this literal selected bound. The stronger
`actual_tail_card_le_on` accepts any explicit challenge finset; the full-field
case instantiates it only after the symbolic proof is finished.

The independent `OffFamilyIntersection`/support-averaging work targets the
high-tail route for the same literal family; its selected endpoint is now checked.
Its role is distinct from the
already completed unique-anchor condition `5*B+255<T`. Four off-family finals
cannot have a common matching support of size a: four-fold interpolation would
construct a family member, and overlap greater than 255 identifies those
finals. Averaging four-way intersections can therefore control the number of
high-matching off-family alphas without demanding one anchor cover every
candidate. Its exact proof/evidence is owned by the accompanying continuation.

## Security implication and stopping condition

The family-coverage tail is new information about adaptive received-word
agreement, rather than another query-last identity. With the selected
instantiation checked, the old curve cap can be multiplied by the actual
query-passing cap in a middle-agreement region instead of charging its entire
roughly 81-bit alpha exception as automatic acceptance. Low agreement is
charged once directly by queries; a separate small high-tail cap handles high
agreement. The final arithmetic requires the parent event partition and
source-shaped query construction. No arithmetic subtotal is claimed as global
security here.

The family contains full quotient-code vectors, including invalid-image
members. Their carried image/row constraints still require joint treatment.
Image-valid family membership is not component membership or payment witness
recovery. Fixed early C1 and the helper degree-two curve suggest a subsequent
three-way support-averaging reduction for gamma, while individual point-error
polynomials remain degree 28. That proposed gamma step is not proved here and
must not assume that every covered quotient has the early C1 projection.

Actual authentication, replay availability, efficient family enumeration,
earlier semantic/copy causality and checked payment extraction remain explicit
obligations. The fixed-family construction is mathematical, not a bounded
extractor. Full-view privacy, resource-bounded Fiat–Shamir and matched complete
transaction CU are unchanged open gates. No grinding contribution is used;
the proof-body model remains 40,282 bytes.

## Focused evidence

`masked-curve-tail-v1.log`: exit 0, 59.81 seconds, peak RSS 4,496,375,808 bytes,
zero swaps; three audits use only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, new axiom, cap increase or unchanged replay. One unused-section
variable warning is nonlogical. Source/olean provenance is unchanged before
and after the focused leaf.

Source SHA-256: `87faa696677db638b53d1258aa9ba8b4971d983255e15e658e5b14bc9df57158`.
Olean SHA-256: `a2e13cff44d43debdb5044b225986f9bafb0c1848829b694797172183dc2c7af`.

Reproduction, with a new log filename for any justified future replay:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_masked_curve_tail.sh LOG
```

The runner uses the cached Lean 4.32.0 environment, `-M7000`, an independent
aggregate 7-GiB child RSS guard and the immutable borrowed source pin. Its
imported degree-three olean matches the already recorded earlier evidence;
there is no cold dependency build or SBF job.

The user subsequently moved all further Lean checks to the NUC. The isolated
workspace is `/home/dombarker/project-offloads/aspis-masked-tail.SH0QtS`; no
shared cache is modified. `stage_masked_nuc.py` stages the exact research and
borrowed source/artifact closure, excluding failed or pending exports. Native
NUC mathlib and third-party compilation artifacts are a declared pinned-revision
cache boundary, not an independently replayed compilation. Each run snapshots
the import manifest, including all newly checked dependency outputs, checks its
hashes before and after, and records successful sources/outputs as immutable.

`masked-curve-representation-nuc-v1.log`: exit 0, 3.07 seconds, peak RSS
6,686,916 KiB, zero swaps, four standard-only axiom audits. Source
`fec35b497ee7be720fcb1546928b021603663364671884a24625f2200b53c7fe`;
olean `4b05402041b1406fa672c76d586fcfcba4ba4a27cb7687f2a5c0c0a297bfffec`.
The imported local research/V7 oleans worked with the same-commit native Linux
Lean toolchain. Actual scope settings were MemoryHigh=5 GiB, MemoryMax=7 GiB,
MemorySwapMax=0, CPUQuota=200%, with Lean `-j1 -M6500`.

The first NUC `OffFamilyIntersection` attempt stopped with interpreter memory
exhaustion before declaration output: exit 134, 3.55 seconds, 6,773,744 KiB,
zero swaps. The unchanged source was not rerun with a larger cap. The new
geometric leaf was split away from its unused causal-game imports; the helper
was then narrowed again to the actual canonical V7 schedule. After these
source/dependency changes and inspection of the native import baseline, the
coordinator approved the separately capped selected-composition profile.
Both narrowed leaves are now green: helper 3.28 seconds / 6,824,612 KiB and
OffFamily 3.10 seconds / 6,827,120 KiB, zero swaps, standard-only audits. Their
exact source and result hashes are in [the high-tail report](off-family-high-tail-review.md).

The unused laptop dependent-runner draft was removed after the NUC switch.
Selected cached-composition checks use the separate
`run_masked_nuc_selected.sh`: MemoryHigh=8 GiB, MemoryMax=10 GiB,
MemorySwapMax=0, CPUQuota=200%, Lean `-j1 -M9500`. The budget is declared before
these new checks because the measured native Mathlib import baseline is about
6.85 GB. This is not an unchanged higher-cap replay of the failed leaf, nor a
cold dependency build. The original 7-GiB runner and its failure evidence stay
unchanged.

`selected-masked-curve-tail-nuc-v7.log`: exit 0, 3.91 seconds, peak RSS
6,845,152 KiB, zero swaps; four standard-only audits. Source
`ba69e4164504fd3da8b2b2e43507924ca8e0dad53959d625648220a6356ac789`;
olean `dcb02d0cdb378b4698d28a09fe6f532a455baf16450f0531249e89d8384ee78a`.
The failed v1–v6 and two diagnostic runs are retained. They isolated concrete
filter/typeclass normalization in the final cardinality wrapper; the actual
fold, own-support representation and validity adapters already elaborated.
The final proof keeps the challenge finset symbolic, uses typed membership
facts, then rewrites the goal with existing masked-good-set and validity
equivalences. It does not unfold a QM31 or Fin262144 enumeration, raise
`maxRecDepth`, add an axiom, or weaken the theorem.

The remote selected command (fresh tag required for a justified replay) is:

```sh
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS/run_masked_nuc_selected.sh /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS SelectedMaskedCurveTail NEW-TAG'
```

Source/olean hashes, import snapshots, cgroup settings and measurements are
retained in the per-run manifests/logs and [transfer receipt](adaptive-tail-transfer.json).
