# Selected classification after the quadratic cover

Status: green on the first focused NUC check, with two standard-only audits.
Source parent: `51692ed712ecb646b51e15e4b8e93e149a6b4014`.

[SelectedQuadraticReduction.lean](experiments/SelectedQuadraticReduction.lean)
composes the exact signatures of `SelectedLinearCover.exists_selected_classification`
and `SelectedQuadraticCover.fixed_cover`. It retains the same actual
`SelectedIdentityCover.Root c1 c2 d gamma Q` premise and the same reconstructed
`exactCircleGRSPolynomial ((atGamma d gamma).original Q)` throughout.

The output chooses both OOD polynomials and the quadratic gamma exception
set before the quantified data d, gamma and Q. It preserves all old terms:

- Linear OOD polynomial: nonzero, degree at most 26854534485.
- Existing `LinearMessageFamily.sparseChallenges`: cardinal at most 3108.
- Existing actual 29-message tuple family: cardinal at most 111.
- Quadratic OOD polynomial: nonzero, degree at most 114687.
- Quadratic exceptional gamma set: cardinal at most 936616.

For a gamma in the supplied fixed universe and the actual Root, the output
is the disjunction of linear OOD-both-roots, the existing linear sparse
challenge event, quadratic OOD-both-roots, quadratic exceptional gamma,
the same-Q retained factor with Y degree at least three, or the unchanged
actual small-tuple representation. The two OOD polynomials are kept separate;
no independently optimistic probability sum or merged root budget is used.

The generic `refine_higher` lemma splits the degree of the *same* factor
from the old higher-degree alternative into two or at least three. For
degree two, its same factor membership, both retained identities and same
candidate root instantiate the checked quadratic cover. It does not replace
the witness with another candidate or an expected honest trace.

The fixed interpolation parent and tuple family depend on C1/C2. Their
earliest justified fixing point is after C2 and before OOD, not before
lambda/chi. The first 26 tuple components still need the separate own-support,
early-C1 and selected semantic/copy/witness bridges. Mathematical family
existence is not an efficient extractor.

The inherited 117077 identity-cover gamma exception is **not** assumed away:
this theorem is Root-conditional. `SelectedIdentityCover.exists_selected_cover`
still supplies the prior exception-or-Root transition under its checked,
circle, west-pole, actual family-membership and image premises. Those premises
are not weakened or asserted as consequences of verifier acceptance here.
Likewise query, rho/later-repair and higher-degree factors are not bounded by
this deterministic classification. No production, protocol, proof-size,
grinding or CU change is made.

## Verified evidence

`Generic.refine_higher` and `exists_selected_reduction` both depend only on
`propext`, `Classical.choice` and `Quot.sound`. No `sorry` or new axiom is
retained. The original V7 proof work is reused through the unchanged selected
classification dependencies; no cold dependency build was run.

The first attempt exited 0 in 3.07s, peak RSS 6865048 KiB, zero swaps.
There were no failed or unchanged repeated attempts for this leaf. Exact
source snapshot, log, per-run manifest and green output are retained as
`experiments/selected-quadratic-reduction-nuc-v1-source.txt`, `.log`,
`-manifest.json`, and `experiments/SelectedQuadraticReduction.olean`.

Source and snapshot SHA-256:
`749a404abe8cf26d2faa81afb28dde00a5dba5e3831811635c27c456aee682e0`.
Olean SHA-256:
`dd51cf75f9036d7bc890073d12b736bb17d9416dc4ddf400abcc5360fe95f0d8`.
Log SHA-256:
`bee91a43b4ed9a659739bdebd5d3b02dd619bfc5fbc1a63e78001964da12cf2f`.
Manifest SHA-256:
`63812b21e1fbd5362f91bea0d003e7c3eb94171346c4450dfda7370616de5cc1`.

Historical command, not an unchanged replay instruction:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedQuadraticReduction selected-quadratic-reduction-nuc-v1'
```

The reused scope retains its creation parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; these are distinct from the new
leaf's source parent above. The prelaunch check found no running user build
scope and 43 GiB available. Lean 4.32.0 ran with `-j1 -M9500`, MemoryHigh
8GiB, MemoryMax 10GiB, MemorySwapMax 0 and CPUQuota 200%. All 847 overlay
artifacts passed the before/after checks unchanged. Native package builds
remain a pinned-revision cache boundary. Tailscale carried the connection;
`nuc.local` was only the verified host-key alias. The sole build slot was
released after terminal postflight; no concurrent V7 process was changed.
