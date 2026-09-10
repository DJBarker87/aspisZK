# Twenty-nine gamma responses to component claims

New leaf: [Gamma29Reconstruction.lean](experiments/Gamma29Reconstruction.lean).
Status: GREEN, focused NUC v1, exit 0 in 3.15 seconds with peak RSS
6,826,220 KiB and zero swaps. All four declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. No probability, accepted-path, shared-support,
payment-validity, or executable-extractor conclusion is claimed.

## Exact finite endpoint

Let `nodes` contain exactly 29 distinct field values, and let each
`candidate gamma : Fin 1024 -> K` be the actual original-message coefficient
vector recovered at that gamma. `reconstructed nodes candidate` is the
coordinatewise degree-28 Lagrange interpolation of those messages. It uses
the existing V7 constructor, not a supplied component tuple or an ambient
code membership assumption.

`nodal_reconstruction` proves `batch gamma reconstructed = candidate gamma`
at every node. For the same three linear functionals and the same 87 scalar
claims at every node, `reconstructed_claims_exact` assumes each of the three
literal equations

    rows row (candidate gamma) = sum lane, gamma^lane * claimed row lane

and proves `claimed row lane = rows row (reconstructed lane)` for all 87
entries. The proof constructs each `ClaimTransport.errorPolynomial`, uses
its degree at most 28 and 29 distinct roots, then reads its coefficients.
It does not replace these three equations by one kappa-weighted scalar
equation, prior zero, or eventual scalar verifier acceptance.

The statements allow arbitrary post-gamma and post-alpha candidate choices.
This is safe for nodal algebra, but does NOT make the resulting tuple fixed
before gamma, lambda/chi, or the semantic sumcheck challenges.

## Reused interfaces and exact limits

V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Working source parent: `556a15569f0dc1d003cf32475091187b206447ec`.

| Existing endpoint | What it supplies; what it does not |
| --- | --- |
| `V7ExactCorrelatedAgreementReleasedLift.releasedInterpolationComponents` and `releasedInterpolationComponents_curve_eq_candidate` | Actual 29-message interpolation and nodal equality. These are used directly. |
| Same module, `exists_exactInitial_components_of_ambient_curve` | Extends equality to a larger selected set only when ONE ambient degree-28 curve and candidate-on-curve correspondence have already been proved. Canonicality at each gamma is not that correspondence. |
| `ClaimTransport.component_error_eval/degree/coeff` | The literal degree-28 scalar-power error and all component coefficients. All three row equations are needed in this leaf. |
| `ComponentRows.point_error` | Converts each actual zero point-row error to the required equation on `Data.original Q`; the source-specific adapter is not part of this generic leaf. |
| `NearGammaCover.interp_on_common` | A common actual support of the 29 encoded responses gives componentwise equality with all 29 received lanes on that support. Distinct nodal canonical responses alone do not give common support. |
| `EarlyC1Family.actual_late_projection_member` and `member_is_base` | At least 38,228 OWN joint symbols put the first 26 components in the fixed pre-lambda family (size at most 100), and base-valued C1 then forces base coefficients. This is not inferred from 29 separate large batch supports. |
| `V7Width29ComponentExtraction.matching_decomposition_selects_exact_components` | Finite component selection assumes `HasMatchingWidth29Decomposition`; it cannot be used to manufacture the missing shared-support fact. |

The older constrained-functional extractor
`V7CorrelatedPointClaimExtraction.many_constrained_gamma_responses_fix_all_point_claims`
has a `PublishedInitialWidth29CurveDecodability` hypothesis. Its published
curve-decomposition boundary is not discharged by the present 29-node lemma
and must not be silently reintroduced to close the retained higher-Y branch.

## Access and fork obligations

One gamma node needs its actual canonical 1,024-coefficient original message,
not merely the 256-coefficient disclosed final. The separately scoped
`SelectedMiddleFourAlpha.reconstruct_middle_canonical` reconstructs the
quotient from four distinct alpha finals PROVIDED each node has an actual
`MiddleWitness`. Its source uniqueness then allows different later histories.
Applying the known affine `Data.original` gives the original message here.
Bare accepted continuations do not establish those witness hypotheses.

Thus the conditional four-alpha route needs 29 distinct gamma nodes and
four suitable distinct alpha nodes at each: 116 qualifying final-vector
observations, or `116*256 = 29,696` disclosed QM31 coefficients (475,136
canonical bytes) in the extractor's multi-run view. This is not extra wire
data in any individual proof. If canonical originals are supplied by a
separately justified decoder oracle, the nodal algebra uses only 29 such
outputs. No such oracle is presumed available from a public Merkle root.

The gamma forks must restore the SAME prefix through C1, lambda/chi, C2,
semantic challenges/answers, all 87 point claims and both OOD answer rows.
They change the gamma answer and its causal continuation. Distinctness and
successful node collection need a stopping/abort policy and a lower bound
on the appropriate success set. Neither 29 nor 116 is a proved bound on
prover invocations, expected work, or ROM rewinds. The fixed strategy model
does not itself grant a programmable random oracle or access to unseen
prover states. A public proof exposes only 22 authenticated raw fibres;
complete received-word support tests require the separately justified hash
query-graph extraction/full-oracle access, not evaluation of expected Q in
place of received data.

The interpolation definition is `noncomputable` Lean algebra. A direct
implementation can build one 29-by-29 Vandermonde inverse and apply it to
1,024 right-hand sides; that is not an executable implementation supplied
here. No extraction runtime or CU measurement is claimed.

## Remaining path to the same-table payment witness

First prove sufficient OWN support for the reconstructed tuple, or another
genuine pre-challenge finite-family membership statement. Then establish
the semantic/copy residuals for that SAME tuple with valid challenge timing.
Exact point claims at one already sampled semantic point do not alone prove
all row residuals: the reconstructed tuple currently depends on later forks.

Once those conditions are available, the checked selected endpoints are:

- `EarlyC1CopyCollision.source_member_covered`: all selected local copy
  residuals, total/inactive helper boundaries and all four active-row poles
  yield weighted aliases OR the existing lambda/chi collision event.
- `SelectedEarlyC1Amounts.member_amounts_or_copy_collision`: amount Boolean
  and recomposition gates, six auxiliary zeros, conservation and positive-pack
  condition yield strict decoded amounts on the same table.
- `SelectedEarlyC1Inputs.member_inputs_or_copy_collision`: actual seven
  registry links derive 72 aliases; non-copy note gates/initial/tail checks
  and public asset/nullifier bindings yield owner, input note and nullifier.
- `SelectedEarlyC1Outputs.member_outputs_or_copy_collision`: output block
  gates, initial/tail checks, amount facts and public bindings give both
  actual decoded output openings. Reuse the same copy exception only once.
- `SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor`, the
  checked input-pair endpoint, `SelectedOutputPair.decoded_outputs_feed_checked_pair`,
  and `SelectedAppendAfterstate.public_output_pair_afterstate` still require
  their literal path/occupancy/append and independently bound snapshot checks.

Authoritative caller/context binding, actual Rust parser/field/hash/compiler
refinement, old-state validity and atomic nullifier/settlement obligations
remain separate. No `validWitness` or successful checked decoder is assumed
or derived by this leaf.

## Verification evidence

Only `Gamma29Reconstruction` was compiled. The first attempt passed, so
there are no failed attempts or reruns. The exact source, source snapshot,
log, per-run manifest and green output are retained locally. The source and
snapshot are byte-identical; the ignored platform-specific olean need not
be committed for publication.

The four audits are `nodal_reconstruction`, `degree28_zero_of_29_nodes`,
`claims_exact_of_nodal_batches`, and `reconstructed_claims_exact`. The log
contains no `sorryAx` or additional axioms. `git diff --check` passed.

The root's serial grant was exercised only after the preceding four-alpha
job explicitly released its slot. The launch preflight found only
`init.scope`, with 49,941,803,008 bytes of available host memory. The runner
used Tailscale `100.108.41.90`, with `HostKeyAlias=nuc.local` only for the
already verified host key. Scope: `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.

The exact launcher was `bash TASK/run_higher_y_nuc.sh TASK
Gamma29Reconstruction gamma29-reconstruction-nuc-v1`. The logged command was
Lean 4.32.0 `-j1 -M9500 -R OVERLAY -o OUTPUT SOURCE`, toolchain commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The cgroup recorded MemoryHigh
8,589,934,592 bytes, MemoryMax 10,737,418,240 bytes, MemorySwapMax 0 and CPU
quota 200%. Existing host swap was not assigned to this job; its measured
swap count was zero. Session 70006 completed with all postflight checks;
the compiler slot was released before the read-only artifact copy.

The inherited runner retains research cache parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the new source parent
above. The per-run manifest passed all 979 pinned entries both before and
after compilation with `PROVENANCE_UNCHANGED=true`. No imports were staged
or rebuilt. Native Mathlib artifacts remain a pinned-package cache boundary,
not a replay of package compilation.

| Artifact | SHA-256 |
| --- | --- |
| New source / exact snapshot | `afee012fe1973aeb7164c7f6a5fba020560050a35311c57206698e8157462ef4` |
| Green olean | `e7b1040892e4c1cf8fe9ece47345e456e27df0bb2077013eb0b89f54b0d3d1ab` |
| V1 log | `c02e9d7824a3a3a4362a377ab5b54fc984f2034f62fea3215faadd6697280796` |
| V1 per-run manifest | `a4f7010471e90e41f653c13fa2a019e8a536bf594179f9a7f3df5b2758e4aa88` |
| Unchanged inherited runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
| Borrowed ReleasedLift source | `83581c24ea8dd1ba7b36aa2d90833d68901111c20b9787a0416bd68cc3bd9612` |
| Borrowed ReleasedLift olean | `3813bf8365ff5b5bc3e8e785c09fc30e2ebab76705ec9c1f4c96f32becaee538` |
| Existing ClaimTransport source | `bc938d4a2765e0a697edc701ac8c2e3aba84a07ebf95bfe3d1fd47e97d693e08` |
| Existing ClaimTransport olean | `6cddaad7b63f0cf8b51d0b6f9c13d67861795374977972f3e05907dcf798155f` |
