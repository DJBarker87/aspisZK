# Candidate security and settlement path

This is a research candidate, not a released 100-bit private spend. The selected
NUC binary now fits two verification-and-settlement transactions for the
ordinary Pool path. The root-history rollover case exceeds the cap with the
v2 adapter and is being optimized. R1 soundness and actual-field privacy
remain separate outstanding gates.

## Selected protocol

Reuse the Pair Forest semantic relation, 29 committed lanes, 22 distinct queried
fibres, M31/QM31 commitments, WideExact gamma and fold challenges, and the R1 S2
two-fold opening. Use D18 transport tau = [3,4,2,0,1], not the P2 placeholder.
The final message contains 64 WideExact values. Only the final residual-batching
challenge rho is narrowed to QM31; gamma, kappa, and both fold challenges remain
WideExact. No grinding/work factor is credited.

For fixed authenticated commitments, fixed final message and sampled queries,
the final equation checks P(rho)=0, where P(T)=sum(i=0..21) residual_i*T^i
over E. If some residual is nonzero, P is nonzero of degree at most 21. An
injective embedding K -> E therefore gives at most 21 bad rho values in K.
The source's 256-bit modulo sampler gives probability at most
21*ceil(2^256/|K|)/2^256, about 2^-119.608. `lean/SubfieldBatch.lean` proves
the algebraic root bound; it does not prove the commitment/Fiat--Shamir glue.
Merkle binding is necessary here: openings arrive after rho, but committed
values must already be fixed except on the separately charged binding event.

## Second fold: concrete parameter route

The preferred route now reuses the existing 256-coefficient matched-response
theorem through a fourfold repeated lift; see `SECOND-FOLD-LIFT.md`. It uses
the existing 9396508281246 challenge cap for both folds. The alternative
smaller parameter calculation below is retained as arithmetic evidence and
is no longer needed on the critical proof path.

The second line code has dimension 64, length 65536 and polynomial degree at
most 63. Proposed minimum agreement is 2390 (strict `ValidResponse` threshold
2389), multiplicity three, weighted degree 7169, X bound 7170, Y rows 113,
and Z bound 2533. The exact interpolation count is 996030138 versus 996016128
constraints, a positive surplus of 14010. Degree 7169 is below 3*2390, and
63*112 <= 7169. The proposed branch-route expression is 120146806070 < 2^37.
These are arithmetic feasibility checks, not a theorem that this encoder has
the required correlated-agreement property.

If at least 9558 initial query fibres match both checks, their parents include
at least ceil(9558/4)=2390 second-fold fibres. Second-fold matching restores a
degree-255 message matching the intermediate committed word on all four
children of each such parent. Its intersection with the original matching
set still contains those 9558 initial fibres, permitting the existing first
fold's extraction route. This is the intended support argument; the new
line-domain fold identities and binding theorem must be supplied.

The initial 29-lane curve and first-fold caps remain in E. Their current
counts are approximately 2^48.3 and 2^43.1, which would yield only about
75.7 and 80.9 bits in K. Narrowing either on the strength of its polynomial
degree alone would ignore the correlated-agreement obligation.

The intended largest per-query error remains the existing q22 expression
(1+delta0)*choose(9557,22)/choose(262144,22), about 2^-105.136. Re-instancing
the second fold, OOD list-to-unique step, semantic/opening glue and rho row is
required before that expression applies to R1. The direct joint-list route
below supersedes the proposed separate OOD uniqueness step. The final FS statement must
retain Qtot and the hash/oracle collision term. It is not an absolute
2^-100 bound for arbitrarily many oracle queries.

## Privacy: actual-field gap found during this investigation

Z4c/Z5 used gamma=7 in K. Its silent lift cancels a lane-c source t with
D=-gamma^(c-28)*t. For actual gamma in E\K that expression need not be K-valued,
so the measured lift does not directly inhabit the actual mask tape. This is
an additional reason not to treat the older rank experiments as a private-spend
proof. The existing D19 spanning and witness-difference image obligations also
remain open. The original cost prover uses deterministic partial fixture masks.
The new `prove_masked_fixture` exercises the complete eligible-noise/H1-padding
tape and full balanced D word, still with explicitly insecure fixture entropy.

Root's candidate repair uses the existing K-valued G and D jointly. Write
Gcoef=gamma^27, Dcoef=gamma^28, and gc=gamma^c in the quadratic K-basis of E.
For det=Gcoef.c0*Dcoef.c1-Gcoef.c1*Dcoef.c0, set

    u=(gc.c1*Dcoef.c0-gc.c0*Dcoef.c1)/det
    v=(Gcoef.c1*gc.c0-Gcoef.c0*gc.c1)/det.

Then gc+Gcoef*u+Dcoef*v=0, with u,v in K. For nonzero gamma outside K the
determinant is nonzero. Add u*t to G and v*t to D, and account for both
their sumcheck effects. Independent G directions disappear from the older
silent-generator family, so its rank must be checked again, not assumed.
The new `privacy-wide` probe tests this exact construction. Even a full-rank
sample would remain evidence, not a universal rank or privacy theorem.

Both actual-field full runs now pass five witness pairs each: gamma limbs
`[7,11,13,17,19,23,29,31]` and `[37,41,43,47,53,59,61,67]`. Each has silent
rank 1076, initial-retained/full-conditioned rank 1080, and five of five
targets contained for both obligations. Receipts are in `evidence/privacy-wide`.
The fresh full-mask native gate passes transfer and withdrawal for S1/S2,
including dense-verifier acceptance and all C1, G, D, and H1 balancing checks.
Neither finite experiment establishes zero knowledge for arbitrary histories.

The proof-driven rank gate also passes on the actual Pool transfer proof:
all 16 eligible C1 ranks 112, H1 padding rank 94/95, and silent-round rank
1076. `PRIVACY-RANK-PATH.md` gives a universal lifting construction to pursue
and records the additional obligations for an optional fail-closed honest
prover. It explicitly distinguishes witness independence from an efficient
simulator and from the separate ROM reduction.

Newer branch evidence `c052a8f09` / `eb4e80c08` independently checks the
actual WideExact R0 payload in Z8 (25/25 target pairs, generic-challenge
silent rank 1076). That is a different payload and transport: it supports
the research direction but is not substituted for this R1 experiment.

## Direct joint-list binding route (root design)

An OOD uniqueness theorem is unnecessary for the following proposed route.
`R0P/SemD2.candidates_card` and `R0P/MaskD2.etaSomeBad_*` already union over
the joint list of at most 100 committed-word candidate tuples. They do not
require a unique tuple. `R0/ListsResponses.Lambda_card` supplies that bound.

Work directly with the committed words W, rather than the chord-quotient
virtual words. After the two-fold extraction described above, obtain a
message q close to the literal gamma-batched W. The existing width-29
matched-response theorem then yields a tuple t in Lambda(W), with
q = sum_l gamma^l t_l. This uses the existing initial bad cap in E.

The six per-lane claims are linear functionals: three multilinear points,
one Libra functional, and two circle evaluations. All their weights and
claims are fixed before gamma. For each of the at most 100 tuples and each
of six functionals, a nonzero per-lane discrepancy is a polynomial in gamma
of degree at most 28. The total extra gamma bad-set cap is therefore 16800.
This is exactly the generic `R0/BadSetBounds.batch_union_bound` pattern.

For fixed gamma, let P_t(X) have constant coefficient equal to the inactive
functional discrepancy and coefficients 1 through 6 equal to the six
batched discrepancies. A false P_t has degree at most 6. Union over the
same list gives at most 600 bad kappa values. Outside that set the accepted
weighted pairing forces P_t=0; outside the gamma set every per-lane claim
therefore matches t. Circle points enter as arbitrary fixed functionals:
no list-to-unique collision probability is charged. Subfield descent and
the existing list-aware semantic extraction then apply to t.

This is a proof design, not yet a compiled R1 binding theorem. It still needs
the exact second-fold code/commutation/restoration instance, both round
polynomial comparisons, and the source/Fiat--Shamir re-instance. It avoids
assuming a unique decoded message or charging a conjectural OOD error.

## Two-transaction settlement architecture

Uploads/staging are outside the user's count. Pool anchor checkpoints are
historical reusable anchors; source accepts retained anchors after newer
checkpoints exist. A 703K-CU checkpoint is not intrinsically required per spend.

Transaction one should authenticate a finalized, verifier-owned proof buffer,
verify the semantic prefix and first ten queries, and store progress bound to
the exact proof and full ASF8 public statement. Transaction two should keep
the existing Pool ASQ8 flow: authenticate current accounts and registry,
CPI into the selected R1 verifier to finish, authenticate its exact ASR8
return data, then consume the nullifier and update lane/history/custody.
The current Tag73-only verifier implementation must gain a distinct R1
profile/release; it must not accept this probe under the old release identity.

The original direct probe keeps progress in a separate account. The existing Pool
CPI forwards a read-only finalized ASPU account, so a concrete integration
can reserve a verifier-owned progress tail in that account. Stage one may
write only that tail after upload finalization; body/public bytes must remain
immutable. Final verification must reconstruct/bind the current public
statement, not trust an uploaded statement without account checks. Such a
buffer can also avoid redundant work by using a proved immutability and
identity invariant. The Pool adapter and protected uploader lifecycle are
now implemented. The v2 adapter retains the full proof/public digest checks
and repeats canonical proof parsing in stage two.

Actual v2 Pool execution on a lane with 13 pairs passes at 1342257/1374214 CU
for transfer and 1340896/1390507 CU for withdrawal. These are measured first
verification / finish-and-settle transactions under the actual 1.4M cap.
Sealing/tail-write/authority/malformed-upload checks, altered-proof, wrong
release, stale-lane, and nullifier replay cases pass with rollback. The
255-pair transfer rollover fails at the CU cap, so ordinary-case fit is not
a universal spend-fit claim. Evidence is in `evidence/pool-v2/`.

No live program was deployed and no funds were moved here. Task keys remain
retained on the NUC; all measured proof entropy is deterministic fixture
entropy and unsuitable for a private live spend.
