# Selected residual recovery bound: focused kernel-checked adapter

[SelectedResidualRecoveryBound.lean](experiments/SelectedResidualRecoveryBound.lean)
is GREEN on its first focused NUC run: exit 0, wall time 2.94 seconds,
peak RSS 6,876,956 KiB, zero swaps and three standard-only axiom audits.
The copied log confirms pre/post provenance PASS1075. The theorem source
is unchanged; its original draft comment is retained rather than causing
an unnecessary replay. Exact copied receipts are listed below.
It imports only `ResidualRecoveryCompositionV8` and
`SelectedResidualHighRecovery`; it does not repeat their gamma counts,
sampler analysis, polynomial construction, or suffix proof.

## Exact connection

`high_probability_eq` identifies the composition leaf's
`highResidualProbability`, specialized to
`SelectedResidualHighRecovery.RecoveredHigh e family`, with the selected
leaf's identically named probability. The only definitional difference is
the selected leaf's `highResidualSlice` wrapper. The equality preserves
the SAME Q, actual witness, adaptive final, and Gamma/G/G/A means; no
concrete recurrence or field computation is reduced.

`residual_partition` instantiates the checked gated partition using
`recovered_high_implies_high` and the probability identity. It concludes
exact equality between the selected higher-unrecovered payoff and the
sum of its actual high-unrecovered payoff and actual LOW payoff. The
suffix is identical on both branches; the event classes are disjoint.

`conditional_nonpair_bound` accepts the SAME explicit fixed-prefix objects
as the selected high-recovery theorem:

- Gamma, family of cardinality at most one, E, beta, sparseSource and bad;
- beta nonzero of degree at most 40 and sparseSource cardinality at most 28;
- exact `sameBad` equality to the shared/sparse/insufficient-own union;
- checked OOD data, circle/non-west conditions, and `CandidateClassifies`
  for the same words, data and supplied objects;
- outside BOTH roots of the literal product
  `E * SelectedSingularOODFamily.obstruction e.c1 e.c2`;
- nonempty A/G/Gamma, `Gamma.card>=6752623450`, and `0<q<=262144`.

The generic product-outside theorem derives the middle `PairRoot`
complement. `high_residual_probability_bound` then derives the selected
`104/Gamma.card` bound. After rewriting the named probability identity,
the checked `ResidualRecoveryComposition.conditional_nonpair_bound`
applies without a supplied high-residual estimate. Its conclusion is

    residualProbability e (RecoveredHigh e family) A G Gamma
      <= 117153/Gamma.card + integratedBudget(q,Gamma,A)
         + q/G.card + 18/A.card.

The last suffix repair is charged once. `integratedBudget` already contains
its conservative cubic `3/A.card` term. No max/sum replacement, independent
marginal product, gamma conditioning, or candidate-family multiplication
is introduced.

## Timing and remaining boundary

The family/E must come from the pre-OOD classification; beta/sparse/bad
and cover are completed-prefix inputs before gamma. They are not selected
again for an observed gamma or final. The theorem consumes that fixed
package and uniformly quantifies the actual later strategy through the
finite means. It does not establish the package's existence at a literal
Rust callback boundary or change the transcript schedule.

The target probability is exactly the composition leaf's gated higher-Y
event. It is not asserted equal to all acceptance or an unrelated earlier
residual probability. Recovery means an actual high witness reconstructs
the family's own-supported tuple; it does not mean `earlyC1=some` or a
checked payment witness.

No additional outer consumer is duplicated here. The checked
`ResidualRecoveryComposition.conditional_continuation_bound` already
provides the trivial outer application once its terminal event domination
is established. The remaining outer step must retain the SAME E/product
root set before both OOD draws, literal source-coordinate/terminal-unit
cases, and explicit history-uniform ordinary law. This theorem neither
infers Fiat--Shamir freshness nor discharges source/authentication coupling.

## Verification status

Module depth is 200, heartbeat budget 250000, with no local overrides.
The source has three `#print axioms` requests and no `sorry`, `admit`,
`native_decide`, or new axiom declaration. The copied successful log was
independently parsed: all three declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or warning. There are no failed attempts
for this leaf. No local Lean, NUC access, cache writes, existing proof
changes, or changes to earlier arithmetic evidence were performed by the
report updater. Receipt verification remains read-only; no unchanged
compiler replay is requested.

## Exact run evidence and provenance

Run tag: `selected-residual-recovery-bound-nuc-v1`. All three receipt files
below are local and their SHA-256 hashes were independently verified:

- [Run log](experiments/selected-residual-recovery-bound-nuc-v1.log):
  `be0583a327efbcc78a487985a84ab6a6a4c04d6698f83c5899dba51999d6de95`.
- [Immutable source snapshot](experiments/selected-residual-recovery-bound-nuc-v1-source.txt):
  `d2ddd1f8cf4fadfaedbf2c8505851c8e300ac413c06e8b33a1d991fb18d534c5`.
  It is byte-identical to the frozen current theorem source.
- [Run manifest](experiments/selected-residual-recovery-bound-nuc-v1-manifest.json):
  `190c68a2a5012c491322f25b462117ac1bd35998dbe1715f3c6a2519cc9081c8`.
- The log records successful output `.olean` SHA-256
  `2b2c22b7dc8cbec9e25a873cf7782cca675004c65e3c9d82a13c692785f82c2a`.
  At report verification the binary itself was not in local EX. This is
  the logged remote post-run digest, not an independent local binary hash.

Both direct imports have registered source/output pairs; their source
hashes also match the local files:

| Import | Source SHA-256 | Registered output SHA-256 |
| --- | --- | --- |
| ResidualRecoveryCompositionV8 | `108953bd2bd14b085c45194d7c1262914ece938731b8b60b9a32a29da724ed3a` | `3ea99bc631c30536e1ead985e09f7e17bda3db075166892b2c9d87074e42c76b` |
| SelectedResidualHighRecovery | `2924bf616df3fdaefd952b61f4ee78c61ef961d605cc7407282692c41b133abc` | `b59a375f064d6292d619d7ce825eb4768344662fb7f40d0061f72907a21b8bf4` |

The manifest contains 1075 registered files; preflight and postflight both
pass, and the log records `PROVENANCE_UNCHANGED=true`. This is an audit of
registered entries, not a complete package replay or a new assertion that
every transitive cache artifact was registered.

The source-work baseline is `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.
The inherited runner creation pin is separately
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, and the borrowed V7 pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. These are cache provenance,
not revisions containing this new theorem. Lean is 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The frozen runner digest is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The coordinator's actual transport was Tailscale
`dombarker@100.108.41.90`; `nuc.local` is only the pinned host-key alias.
The task was `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX` and
the recorded command was the one-file Lean invocation

    lean -j1 -M9500 -R TASK/overlay -o TASK/overlay/SelectedResidualRecoveryBound.olean TASK/overlay/SelectedResidualRecoveryBound.lean

Its systemd scope recorded `MemoryHigh=8589934592`,
`MemoryMax=10737418240`, `MemorySwapMax=0`, and
`cpu.max=200000 100000`. Measured wall time was 2.94 seconds, peak RSS
6,876,956 KiB and swaps zero. All source, event and probability boundaries
above remain unchanged by this successful kernel check.
