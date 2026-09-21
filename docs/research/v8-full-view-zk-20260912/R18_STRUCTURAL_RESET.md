# R18 sparse code-coordinate G — measured research boundary

Base: `6677d5f1310ff7373301fbd79f186278f772e68a`.
Local branch: `research/v8-r18-sparse-coded-g-20260921`.
First profile: `AV8/R18/sparse-coded-G128-step3/two-channel/research-v1`.
Second profile: `AV8/R18/sparse-coded-G128-step3/minimal-T163/research-v2`.
No deployment, wallet operation, merge, or push.

The original privacy branch and preferred R43 endpoint are preserved. The
new profile changes the semantic G coins, not merely the FFT implementation.
It is therefore intentionally transcript-incompatible with R17/v2. The first
profile retains current T and pivot 1023. Only after its source and SBF gates
did the second profile activate the minimum-support T; it retains the same
first 89 pad images and pivot. Production protocol paths are unchanged.

## Implemented boundary

`stage_r18_sparse_g.py` verifies the retained R43 control pins, then creates a
fresh source-screening copy. Semantic coins are `G[order[128+3*i]]`. Producer,
initial claim, selected point, audit rows, dense reference, and optimized
dense functional adapter all use that same map. The ten-round polynomial
formulas and eta-after-initial chronology are unchanged. The 953-field frame,
both final arrays, all image/query terms, and both host verifiers remain.

`stage_r18_compact.py` adds a same-profile compact primary. It uses caller
scratch for 271 coin coefficients and 128 grouped sums; no G tree/FFT or
dense G functional is required in the primary. The base terminal is
`dot(R+G,A) + kappa*dot(G,H-E)`. Separate fresh-query and image contributions
remain. The internal opening reference cross-check is still retained.

The independent double verifier remains the host default. A distinct
`r18_primary_only` SBF build flag omits only the second complete verifier;
this saving must never be subtracted from the historical primary checkpoint.
The primary still performs the original parsing/domain/authentication and
relation checks. Actual source/table/frame gates and runtime results are
recorded below; supported-budget execution remains unsuccessful.

## Evidence so far

- Packet SHA256: `894f64be2685fd8f1f4b69cc99a9244802765012b8d76e5ae8cf5478211a0fd1`.
- All 26 packet manifest entries verified; all eight supplied Git source pins
  match the base. Full optimized C++ model preflight passes: 63 rank cases,
  295 sparse terminal cases, codec/dual and sharing controls. These are model
  checks, not extracted Rust or source privacy proofs.
- Actual Rust sparse terminal versus retained grouped kernel and independent
  chord/four-fold calculation passes 32 challenge cases, each with 271 basis
  coins, plus arbitrary vectors. Zero and one challenges are included.
- Local focused compact check `/tmp/r18-shared-check-b` passes 32 cases against
  dense source dual/chord/fold: A, first-point E, sparse H, complete G,
  both interpolant branches, and arbitrary two-channel pairing.
  `rustc -C opt-level=2` with existing cached core/statement dependencies;
  runtime exit 0, wall 0.96 s, peak RSS 2,359,296 bytes, swaps 0.
- First source witness passes actual C1 correction (16 columns, 108 rank per
  column), H1 (562 equations, rank 540), G (625 equations, rank 601), semantic
  cancellation, seven relation coefficients, 88 raw openings, OOD, point,
final and mask-legality checks. Both complete host verifiers accept.
- Corrected second witness independently passes the same complete source
  correction. Its proof SHA256 is
  `54ab100b7f1792e096b61840a64c8ec787520ac8f517ebcde932df46cc7de8e8`,
  distinct from world0
  `afd4bab9e6746c8394a57fe37339c028ccb9b0014199870132e0c144484b863e`.

Source matrices now have distinct test-only `SparseCodeRelation` and
`SparseCodeJoint` dispatches. Existing Original, First271 and Vandermonde
controls remain unchanged. Both 624/625-row tests pass at both real prefixes,
rank 601 in all four cases. Raw journald capture is retained separately from
the initial condensed worker summaries; only raw capture is release evidence.

## First-profile SBF measurement

Primary ELF SHA256:
`efaaaabe6d4cdea5fc92da53da38560b0984e336c3c5f8cde6b2cba57c80180d`.
Actual source/frozen-table and frame gates pass. Same pinned v1.54 toolchain,
256 KiB heap, primary flag `--cfg r18_primary_only`; no settlement adapter.

| New-profile input | Primary whole-program CU at diagnostic cap | Outcome |
|---|---:|---|
| World0 honest | 5,623,539 | Accepted |
| World1 honest | 5,617,580 | Accepted |
| World0 corrupted G final | 1,880,198 | Completed rejection, Custom(6) |
| World1 corrupted G final | 1,873,127 | Completed rejection, Custom(6) |

**Both 1.2M and 1.4M limits still exhaust.** The diagnostic cap is not a
supported transaction budget. Against historical R43's primary checkpoint
16,456,519, world0 is about 66% lower (different explicit protocol profile and
new proof; this is not a same-proof arithmetic-only comparison).

World0 stage differences from instrumented remaining-CU markers:
semantic 732,790; preparation 317,273; opening points 79,522; opening records
536,365; paired authentication 138,192; internal reference after authentication
872,298; fresh-query injection 55,830; tail folds 270,641; shared A/E terminal
1,968,019; sparse G terminal including coefficient construction 534,349.
These checkpoint differences include intervening instrumentation/overhead.

The separate double-verifier ELF
`3b28026adde6800d7cc0db9f8a7d69e436f727535714ee2f0f8009f179f84e6d`
still heap-fails in its reference pass: 15,318,226 CU honest and 11,603,350 CU
corrupted G. Neither failure total is an accepted verifier CU count. The
primary succeeds independently; the dense reference remains in host testing.

## Second profile and best measured implementation

`stage_r18_minimal.py` constructs T from the actual source pad inventory,
checks the first-profile accepted SBF evidence, and assigns a new profile ID
from transcript initialization. It changes 163 coordinates instead of 479.
The frozen SBF order/inactive table is checked against the host constructor
before compilation. The ordinary correction evaluates only those 163 slots;
it does not merely allocate a smaller dense prefix.

Both new genuine source prefixes pass C1 correction, the 562-row H1 system
(rank 540), and the 625-row G affine system (rank 601, 24 compatibility
relations), with the actual opposite-witness target and retained semantic,
relation, raw, point, OOD, final and mask-legality equations. The source
constructor check covers permutation/dual inverses, all 89 balanced pad
directions, pivot and column legality, including full-QM31 samples. This is
executed source evidence, not a universal theorem. Recipient-zero and
change-zero witnesses fail at the semantic check, Custom(4), with genuine
terminal polynomials and no forced future challenges. An earlier-profile
proof is rejected. See `evidence/r18-minimal-b`.

The first minimum-T implementation measured 4,843,133 / 4,846,265 CU for the
two honest worlds. Its primary ELF is
`95c61d4a22c2a3c63c6776b5c26257a4b0fe0a3a2d3c3222e3ea11a5aba364df`.
The final same-profile arithmetic specialization represents fixed powers of
one-half in M31 and uses scalar multiplication, instead of full-QM31
multiplication. It changes neither coins nor transcript. Sparse/dense,
codec/dual and shared-ordinary release checks pass, and both existing
minimum-T proofs pass both host verifiers unchanged.

| Final implementation, 256 KiB heap | Whole-program CU at 100M diagnostic cap | Outcome |
|---|---:|---|
| World0 honest | 4,781,147 | Accepted |
| World1 honest | 4,784,274 | Accepted |
| World0 corrupted G final | 1,879,312 | Completed rejection, Custom(6) |
| World1 corrupted G final | 1,878,159 | Completed rejection, Custom(6) |

Primary ELF SHA256:
`94589c592945a41fdc9d3d2b529de2fc60e65e7ea24aa3a69c96820e614ff916`.
Build exit 0, wall 65.51 s, peak RSS 619,900 KiB, swaps 0; actual frame and
source/table gates pass. The same-profile arithmetic saving is 61,986 /
61,991 CU. The approximately 71% reduction from R43 is a **different-profile**
comparison, not a claim that the old proof verifies more cheaply.
**Every 1.2M and 1.4M run still exhausts. There is no supported-budget result.**

Final world0 checkpoint differences: semantic 732,945; preparation 317,203;
opening points 79,467; records 536,380; authentication 141,246; internal
reference after authentication 875,150; query injection 55,851; tail folds
270,774; shared A/E terminal 1,181,639; sparse G terminal 472,227 CU.
These include intervening instrumentation. Removing the independent internal
cross-check is not justified yet: redundancy for arbitrary canonical inputs
and all source error cases must be established first.

The final diagnostic (double-verifier) ELF is distinct:
`edce79a75d7c3e75a06db6fa586e7a6622a30b43ff0c8962930cfac5f3011518`.
Build exit 0, wall 40.10 s, peak RSS 619,524 KiB, swaps 0. At 100M it heap-fails
at 14,405,605 CU honest / 11,535,930 CU corrupted G; neither is accepted CU.
Its 1.2M/1.4M cases exhaust. Evidence: `evidence/r18-minimal-base-a`.
The retained simulator's generic JSON scope/markers still say R17; the ELF
hash, source manifest and explicit R18 profile identify the tested artifact.
All SVM runs are local simulation without settlement, RPC or wallet use.

### Internal reference audit

In the pinned staged `r17_host_relation::opened`, the primary already does
selected-point construction, all-limb packed canonical decoding, C1/C2 leaf
hashing, base-coordinate/chord-pole checks, quotient construction for each
channel, four-fold evaluation and paired Merkle authentication. It then
calls `relation_callback::opened_values_reference`, which independently
repeats point selection, canonical gamma combination, leaf hashing,
individual inversions, folding and the same paired authentication on the
combined channel. The final equality of line points and
`reference[i] = R[i] + G[i]` is an additional differential assertion; it
must not simply disappear on the evidence of honest fixtures.

The exact removal obligation is equality of selected points, canonical
decoder results, channel-sum quotient/fold values and authentication results
for every parser-valid input, plus preservation of Domain/Canonical/
Authentication/Terminal failure behavior. In particular, the primary batch
inverse fallback and earlier zero-coordinate check must correspond to the
reference's per-record inversions and check ordering. This source refinement
has not been proved here, so the call and its full cost remain. The separate
second verifier is omitted only in the explicitly named primary SBF build;
the host default and diagnostic SBF retain it. Neither image constraints,
44 query consistency equations nor final relation acceptance were removed.

## Focused formal result

Eight declarations in `lean/AspisV8R18/SparseCoordinates.lean` compile: slot
injection, selected 271 / retained 752 cardinalities, retained-index
characterization, both generic codec inverses, arbitrary channel pairing,
and invertible-transport cancellation. Axioms are only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom. Exact hash,
command, wall time 5.45 s, RSS 1,458,733,056 bytes and zero swaps are in
`evidence/r18-sparse-coordinates-lean.json`. This does not close grouped
Rust/chord refinement or any probabilistic/security obligation.

## Rejected attempts / audit corrections

1. First source compile rejected two `Vec<usize>` versus `[usize;1024]`
   adapter mismatches. Exact array views fix the adapters; no premise changed.
2. A checker's formatter recursively formatted the retained R43 grouped
   module. Pin validation caught it. Only that attributable formatting edit
   was restored from the verified predecessor; the checker now uses portable
   sibling imports. No pin was waived.
3. An initial shared-E draft computed the sum of all three MLEs plus the
   inactive vector, rather than just the first MLE. It was not accepted.
   Lead review replaced the implementation and independent reference, also
   correcting the missing second A tensor in the permutation correction.
4. The first two-world runner used an obsolete `ASPIS_R15_SELECTED_SECOND`
   variable, but this source reads `ASPIS_R16_SELECTED_SECOND`. The identical
   accepted prefixes exposed the error. The two runs are one-witness evidence,
   not two-prefix coverage. The corrected missing-world replay passes;
   the runner now also checks that two selected worlds yield distinct prefixes.
5. The initial minimum-T test incorrectly used an unbalanced unit direction
   and insufficient extension-field variation. The corrected test uses the
   actual source pad rows, balancing pivot and full-QM31 inputs.
6. Broad Mathlib import exceeded the focused Lean cap. Six narrow imports
   and generic symbolic codec lemmas replaced the broad import and concrete
   Fin reduction; no memory cap or theorem premise was weakened.
7. The first standalone source-test worker logs were condensed summaries.
   Raw journal captures were recovered and checked against the test binary
   and source hashes. The four requested scopes used 5G/7G/zero-swap settings,
   but their live cap properties were not retained before collection; the
   README records that evidence limitation. Main source/runtime gates have
   live cap artifacts. Precondition/compile failures remain in the ledger.

## Reproduction and retained artifacts

Use the pinned R43 adapter chain, then `stage_r18_sparse_g.py` and
`run_r18_source_gate.py` for both genuine worlds. Next use
`stage_r18_compact.py`, its sparse/shared release checkers, and
`build_r18_sbf.py --mode primary` / `--mode diagnostic`. Run the pinned SVM
probe separately on each named ELF. Only then use `stage_r18_minimal.py`
with the accepted first-profile JSONL, repeat the new-profile source gates,
and apply `stage_r18_base_scaling.py` for the final arithmetic specialization.
Every staging output must be fresh; all input manifests are validated.

Heavy builds/elimination ran on the Tailscale NUC in bounded, zero-swap
systemd scopes with cached release/SBF targets. Generated stages and proof
fixtures remain in `/home/dombarker/project-offloads/aspis-r18-*`; they are
not installed over the production source. The final source hash manifest is
retained with its evidence. The small focused Lean leaf uses the existing
local cached `AspisFormal` workspace. No unchanged full formal suite ran.
Stage manifests describe inputs before execution (their initial gate booleans
are not retrospective verdicts); raw gate logs and ELF hashes record outcomes.

## Security boundary

None of the finite checks proves universal compatible-image coverage,
adaptive exceptional-prefix probability, seed-expansion/oracle replacement,
or public-only complete simulation. In particular, 271 selected ideal mask
coordinates are not a claim that the real seeded coins are independent.
No new hiding, uniformity, or rank assumption has been introduced.

The first unresolved mathematical statement is, for source-valid prefixes
outside a justified bad event, `Im M_G(prefix) = ker C(prefix)` for the full
625-row sparse-G map (rank 601 and 24 compatibility relations), together
with membership of the actual C1/H1 affine target. For minimum-T, the old H1
active-minor/certificate index correspondence must be rebound; it cannot be
inherited by name. Both real-prefix tests are screening evidence, not that
theorem. The exceptional event then needs a quantitative adaptive bound
under the real shared seed/oracle first assignments, transcript selection,
retries and publication. Public-only complete simulation and soundness
remain separate obligations. No IID substitution or new hiding assumption
closes any of them.

No full privacy theorem, soundness closure, or supported-budget SBF execution
has been established. Do not report the packet complete or promote either
new research profile as a released protocol. The immediate performance
blocker is the remaining 4.78M versus 1.4M budget gap, independently of the
universal security obligations above.
