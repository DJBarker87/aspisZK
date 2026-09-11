# Middle/high gamma probability composition

Checked and frozen: [NestedCircleContinuationV2.lean](experiments/NestedCircleContinuationV2.lean)
and [SelectedMiddleGammaProbability.lean](experiments/SelectedMiddleGammaProbability.lean).
The two green leaves have fourteen standard-only axiom audits. The first
continuation attempt is preserved as a diagnostic, not theorem credit.

## Exact event and result

`SelectedMiddleGammaProbability.probability_bound` proves

`eventMass ≤ 65061549*65061548 / (N*(N−1)) + 117145/|Gamma|`,

where `N=(2^31−1)^4−(2^31−1)^2` and Gamma is the original finite challenge
set. The theorem does not replace Gamma by its nonexceptional subset or
condition on OOD success.

`eventMass` is the continuation-valued nested circle-three/distinct-three
kernel, whose terminal reward is the existing
`SelectedHigherYProbability.highProbability`. Thus it counts the actual
high-support higher-Y prefix, weighted by the same compact suffix once,
with the original gamma/kappa/tau/alpha means. The final polynomial remains
selected after alpha by `Execution.strategy`. This is not a bound on all
acceptance, the low-support branch, or payment failure.

The lower support threshold is 200808 complete quotient fibres, as derived
by `SelectedMiddleGammaCover.high_prefix_mem`. Its fixed-C1/C2 cover is
stronger than the event and needs no early-C1 success, regularity,
own-support or extra candidate-membership premise. The 117145 cap is the
previously proved union bound `40+28+117077`; this leaf does not add a second
specialization or shared-suffix repair.

## Causal interfaces and proof map

The order in the mathematical experiment is fixed C1/C2, first OOD draw,
`between` history update (which can absorb the first answer), distinct
second OOD draw, terminal history/data, gamma, then adaptive later choices.

| Checked interface | Role |
|---|---|
| `NestedCircleContinuation.Generic.distinctPay` / `pairPay` | Retain the actual terminal history through every duplicate retry; ordinary failure or exhausted retries pays zero. |
| `pairPay_indicator` | Finite linearity identifies root-pair indicator payment with the existing sum of ordered distinct target masses. No sampling law is needed. |
| `actual_exception_bound` | A history-dependent reward bounded by the root-pair indicator plus b has mass at most `targetMass+b`. |
| `SelectedMiddleGammaCover.exists_selected_cover` | Selects E before all OOD data, with E nonzero and degree at most 65061549; outside its pair-root event, the whole middle-gamma set has cardinality at most 117145. |
| `high_card_bound` / `high_unit` | Bound the actual high-prefix suffix by the middle-gamma indicator or by one, respectively. |
| `terminal_bound` | For every legal distinct pair and terminal history, bounds its actual gamma reward by the complete-root-pair indicator plus `117145/|Gamma|`. |
| `MiddleSimplePairMass.pair_root_mass_numeric_le` | Applies the checked abort-preserving mass theorem to the SAME E from the cover, not a separately chosen obstruction. |
| `probability_of_cover` / `probability_bound` | Compose these ingredients with the terminal continuation; no history is selected merely as a function of the OOD pair. |

The explicit `finish : K → K → H → Execution q` receives both successful
parameters and the actual terminal history. `SourceAt` requires that this
execution has the same fixed C1/C2, checked data, circle equations, non-west
guards, and exact coordinate equalities
`SelectedOODGate.point data 0=first`, `point data 1=second`. These fields
are premises, not a newly proved byte/controller decoder refinement. The
cover is valid for arbitrary such terminal data; consequently it does not
need to assume that all histories with the same pair have identical
answers or continuation strategies.

The source theorem assumes nonempty coin, A, G and Gamma sets and
`q≤262144`. It retains the explicit history-uniform ordinary law
`NestedCircleMass.Generic.Uniform coins draw ordinaryAtomMass`, where the
atom mass is the checked actual `OrdinaryPrefixMass.value` success mass
divided by the field cardinality. Reused V7 decoder formalization supplies
that unconditional atom value, not freshness at every later history.
The displayed Gamma/G/A averages specify the mathematical experiment;
they do not prove fresh transcript challenges. Literal controller/tape
refinement, history freshness, Fiat–Shamir/ROM, byte and CU claims remain
outside this result. No transcript changes are proposed.

## Focused evidence

Source worktree parent: `2f92bdd5f08fa89060c85262a55c19545a002064`.
Parent launched each focused check serially over Tailscale on the inherited
`aspis-higher-y.fMoMeX` workspace. No local or package-wide compilation was
performed. Source/cache pin `289d7356c78a4cd493fe61a54f9548f2a0c11298`,
borrowed V7 pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`;
Lean 4.32.0 with `-j1 -M9500`. All attempts retained recursion depth 200,
heartbeats 250000, MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and
CPU 200%. The frozen [runner](experiments/run_higher_y_nuc.sh) has SHA256
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

| Target / tag | Exit | Wall | RSS KiB | Swaps | Provenance | Audits |
|---|---:|---:|---:|---:|---:|---|
| `NestedCircleContinuation`, `nested-circle-continuation-nuc-v1` | 1 | 6.58 s | 6816876 | 0 | 1037 preflight | diagnostic only |
| `NestedCircleContinuationV2`, `nested-circle-continuation-v2-nuc-v1` | 0 | 3.16 s | 6850708 | 0 | 1041 unchanged | 8 standard-only |
| `SelectedMiddleGammaProbability`, `selected-middle-gamma-probability-nuc-v1` | 0 | 4.91 s | 6898240 | 0 | 1043 unchanged | 6 standard-only |

V1 had two elementary proof-plumbing failures: a remaining `if True`,
and the wrong orientation of an addition monotonicity lemma. V2 adds
`if_true` and uses `add_le_add le_rfl constant`; it changes no definitions
or limits. Six harmless unused-section/simp warnings remain in V2; the
selected leaf has no warnings. Every green audit uses only `propext`,
`Classical.choice`, `Quot.sound`. All three source/log/manifest triplets
and both green olean files are local and hash-verified.

Exact SHA256 inventory:

- Continuation V1 [source](experiments/nested-circle-continuation-nuc-v1-source.txt)
  `665b423d3f692267bc00a5751d0c18678254aa068d7a8221771f9d05136e6b6f`;
  [log](experiments/nested-circle-continuation-nuc-v1.log)
  `55059548378d42503e124be9a7c3f10777cb3d5e5263cd7d5370bffe1dbcd61c`;
  [manifest](experiments/nested-circle-continuation-nuc-v1-manifest.json)
  `4abe6da1d7bb6e02c1ec128962358a4f6cd7b53677aa6b706ebbb2922a499fc6`.
- Continuation V2 [source](experiments/nested-circle-continuation-v2-nuc-v1-source.txt)
  `b41d00c49af2e157eacb3ea26aaed82e184f0f469b750e57b9b9000cccea606d`;
  [log](experiments/nested-circle-continuation-v2-nuc-v1.log)
  `c0a1e739652eb77bf950afddddf271f29412c1aafb6240a601c3541b67fa2fc6`;
  [manifest](experiments/nested-circle-continuation-v2-nuc-v1-manifest.json)
  `e1ca74d3887394dab91e2665080b2803a73d03e042db2902babfd36b18bbdf0d`;
  olean `adb6e41d3d5eced350b8829544c6971c48b9f59021c599526594960caf618f54`.
- Selected [source](experiments/selected-middle-gamma-probability-nuc-v1-source.txt)
  `20bb477e3abe60fa997f9ec0e57a964c8691a93254cc6fa47e4eca6874d577eb`;
  [log](experiments/selected-middle-gamma-probability-nuc-v1.log)
  `155cc9aeadff6d6a240ddd322639a614caf949188db29fab74c533c5ccfd90f5`;
  [manifest](experiments/selected-middle-gamma-probability-nuc-v1-manifest.json)
  `8f6b3ed81cf71c84e1535f32ef47af6e3237ed15ab53be1470f3ce10692c44e1`;
  olean `b61905b7d202e22e5ef20f42ae68fddbb50b2efa800254ce191c5e9ae9b295ff`.

The source files and evidence are frozen. No further theorem work or build
is pending for this scoped gamma composition.
