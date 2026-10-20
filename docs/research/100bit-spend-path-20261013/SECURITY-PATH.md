# Candidate security and settlement path

Dated note (2026-10-20): the [binary-multiproof ledger amendment](../v8-r1-20261011/R1_SOUNDNESS.md#amendment-for-the-binary-multiproof-format-2026-10-20)
records the adopted frozen format, binary collision allowance, verifier query
budget, query-scan abort, privacy read budget and successful stage-1 route,
with source and proof evidence. It preserves the earlier text as history and
states the remaining refinement conditions.

This is a research candidate, not a released 100-bit private spend. The selected
NUC k11 binary now fits two verification-and-settlement transactions for the
tested ordinary and rollover Pool paths (13, 255 and 1,023 populated pairs).
The optional P3 salted-commitment path also passes all six cases with fresh
OS-generated full masks. Three independent mask draws for the same transfer
statement fit, with a measured 284 CU stage-one spread and 171 CU terminal
spread; these are finite measurements, not a constant-cost theorem. R1 soundness and actual-field privacy remain separate
outstanding gates; a roughly 105-bit proposed per-oracle-query coefficient is
not an implemented security theorem.

The latest reuse checkpoints add a conditional unified Fiat–Shamir bound,
independent-answer bounds for the four opening challenges, and a whole-word
two-pad correction. They still leave an explicit knowledge-extraction and
committed-word boundary: the old existence extractors and Boolean-decision
verifier do not establish recovery of a spend witness from the actual
Merkle/oracle experiment. See [the audited boundary and continuation](KNOWLEDGE-AND-ORACLE-BOUNDARY.md),
[opening bounds](OPENING-SAMPLER-BOUNDS.md), and
[pad correction](DUAL-PAD-WORD-BRIDGE.md).

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
21*ceil(2^256/|K|)/2^256, about 2^-119.608. `lean/QueryResidualBridge.lean` now connects the explicit accumulator
recurrence to this residual polynomial. `lean/RhoSamplerBound.lean` proves
the independent-answer modulo density, and `lean/RhoAcceptance.lean` bounds
acceptance when a fixed query misses the matching set. The byte/field rank
encodings and commitment/Fiat--Shamir glue remain separate obligations.
`lean/SamplerNatModel.lean` now derives the intended 4/8-digit modulo laws
from natural-number division and carry models, with positional tuple ranking
and the concrete quotient bound; it does not prove Rust refinement. See
`SAMPLER-TRANSPORT.md`.
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
fold's extraction route. This support argument, the actual stored line-domain geometry, both
restoration steps and the identification with a member of the literal joint
list now compile through `TwoFoldExtraction.lean` and `ConcreteBinding.lean`.
The matching equations are still field-level premises, not consequences of
proved Rust/Fiat--Shamir correspondence.

The initial 29-lane curve and first-fold caps remain in E. Their current
counts are approximately 2^48.3 and 2^43.1, which would yield only about
75.7 and 80.9 bits in K. Narrowing either on the strength of its polynomial
degree alone would ignore the correlated-agreement obligation.

The intended largest per-query error remains the existing q22 expression
(1+delta0)*choose(9557,22)/choose(262144,22), about 2^-105.136. The concrete second-fold extraction and direct joint-list binding now
compile. `lean/BoundedQueries.lean` now applies the existing bounded, stopped
sampler theorem to the concrete matching set under independent-answer
semantics, without conditioning on success. The source/shared-oracle
instantiation and semantic/opening glue are still required before that
expression applies to R1. The direct
joint-list route below supersedes the separate OOD uniqueness step. The final FS statement must
retain Qtot and the hash/oracle collision term. It is not an absolute
2^-100 bound for arbitrarily many oracle queries.

## Privacy: actual-field gap found during this investigation

Z4c/Z5 used gamma=7 in K. Its silent lift cancels a lane-c source t with
D=-gamma^(c-28)*t. For actual gamma in E\K that expression need not be K-valued,
so the measured lift does not directly inhabit the actual mask tape. This is
an additional reason not to treat the older rank experiments as a private-spend
proof. The existing D19 spanning and witness-difference image obligations also
remain open. The original cost prover uses deterministic partial fixture masks.
`prove_masked_fixture` exercises the complete eligible-noise/H1-padding tape
and full balanced D word with explicitly insecure fixture entropy. The P3
`prove_masked_attempt` path now uses reserved OS-generated attempt secrets
and a durable nonce ledger; actual Pool runs exercise that path. Neither API
contains a proved rank/publication guard or a full zero-knowledge theorem.

Root's candidate repair uses the existing K-valued G and D jointly. Write
Gcoef=gamma^27, Dcoef=gamma^28, and gc=gamma^c in the quadratic K-basis of E.
For det=Gcoef.c0*Dcoef.c1-Gcoef.c1*Dcoef.c0, set

    u=(gc.c1*Dcoef.c0-gc.c0*Dcoef.c1)/det
    v=(Gcoef.c1*gc.c0-Gcoef.c0*gc.c1)/det.

Then gc+Gcoef*u+Dcoef*v=0, with u,v in K. For nonzero gamma outside K the
determinant is nonzero. This implication and the embedded 27/28-power
correction now compile for a rootless quadratic extension in
`lean/DualPadQuadratic.lean`; source and mask-layout correspondence remain
open. Add u*t to G and v*t to D, and account for both
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

The proof-driven rank gate also passes on the actual fresh-OS, salted P3
Pool transfer proof (`evidence/privacy-wide/proof-rank-gate-p3/`):
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

The generic direct-functional comparison now compiles in
`lean/JointFunctionalBinding.lean`: it derives the discrepancy polynomials
and all per-lane consequences, with the 16,800/600 bounds.
`lean/TwoRoundPairing.lean` also derives both true round boundaries from
the specified folds and performs the two comparisons. `lean/ConcreteBinding.lean` now combines the concrete stored-domain
restoration/extraction, the literal joint list and its cap, both comparisons,
and weights derived from the six linear functionals. It proves a deterministic
field-level binding theorem with explicit matching-support, accepted-equation
and bad-set-exclusion premises. Identifying the actual Rust functionals and
verifier equations with this model, and the complete transcript/query/Fiat--Shamir
instantiation, remain open. No uniqueness premise or conjectural OOD error is used.
See `CONCRETE-BINDING.md` and `QUERY-BINDING.md` for the exact scope and
NUC receipts. The subsequent `LEAN-REUSE.md` checkpoint derives candidate
subfield typing and the original point/extra/codeword-typing witness interface
from the concrete opening, with explicit E-valued rows.
`MaskedSemantic.large_matching_extracts` now also connects that candidate
to the existing masked semantic core and input-note extraction, under the
explicit list-wide semantic bad-event exclusions. The query/residual field
equations and independent-answer laws compose at the model level. Source
correspondence, supplying and bounding those exclusions for the new
transcript, and the shared-oracle instantiation remain open. See
`MASKED-SEMANTIC-BRIDGE.md`; this does not establish full settlement or privacy.

The later `SemanticPrefix.large_matching_extracts_of_prefix` derives the
semantic candidate exclusions from the first 25 parsed prefix events,
including the old pre-C2 padding argument for lambda/chi. It uses no old
opening tail. The existing independent-answer per-prefix bounds have a
checked sum `303100 * (1+deltaQ)/P^4`; shared-oracle accounting and source
correspondence are still required. See `SEMANTIC-PREFIX-BRIDGE.md`.

`SpendExtraction.large_matching_extracts` now strengthens the same candidate
to bounded natural values with integer conservation, input-note extraction,
and recipient/change note commitments under the actual variant/Option guards.
It reuses the existing production value, copy, Poseidon, schedule, asset, and
digest theorems; no positivity lane is assumed. This closes the note-level
deterministic extraction extension, not append correctness, source refinement,
shared-oracle soundness, or privacy. See `SPEND-NOTE-BRIDGE.md`.

## Two-transaction settlement architecture

Uploads/staging are outside the user's count. Pool anchor checkpoints are
historical reusable anchors; source accepts retained anchors after newer
checkpoints exist. A 703K-CU checkpoint is not intrinsically required per spend.

Transaction one should authenticate a finalized, verifier-owned proof buffer,
verify the semantic prefix and first eleven queries, and store progress bound to
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
and repeats canonical proof parsing in stage two. The subsequent adapter
skips the redundant field scan only under the checkpoint provenance and
byte-identity invariant audited in `AUTHENTICATED-PARSER-AUDIT.md`. This
includes an explicit deployment-history premise; an unkeyed checkpoint
checksum does not establish provenance.

Actual v2 Pool execution on a lane with 13 pairs passes at 1342257/1374214 CU
for transfer and 1340896/1390507 CU for withdrawal. These are measured first
verification / finish-and-settle transactions under the actual 1.4M cap.
Sealing/tail-write/authority/malformed-upload checks, altered-proof, wrong
release, stale-lane, and nullifier replay cases pass with rollback. The
255-pair transfer rollover fails at the CU cap in v2. Evidence is in
`evidence/pool-v2/`. The later k11 adapter moves one query into stage one:
measured terminal CU at 13/255/1,023 pairs is respectively
1,295,281/1,361,386/1,357,996 for transfer and
1,311,593/1,377,495/1,374,341 for withdrawal. Stage one ranges from
1,387,210 to 1,388,644 CU. These concrete cases fit the 1.4M cap; they do not
prove a uniform maximum over all statements, masks or account histories.

The default-off P3 feature adds private leaf salts and distinct proof,
transcript, profile and release identities. Fresh-OS full-mask runs, on one
frozen P3 ELF, report the following actual v0 transaction CU:

| Populated pairs | Transfer tx1 | Transfer settle | Withdrawal tx1 | Withdrawal settle |
|---|---:|---:|---:|---:|
| 13 | 1,390,049 | 1,293,584 | 1,388,879 | 1,309,815 |
| 255 | 1,389,907 | 1,359,784 | 1,388,574 | 1,375,920 |
| 1,023 | 1,389,978 | 1,356,607 | 1,388,652 | 1,372,691 |

Two additional independent OS draws for transfer/13 reach at most
1,390,333 / 1,293,755 CU. The tightest observed headroom is 9,667 CU in tx1
and 24,080 CU in settlement. The deterministic full-mask control is inside
the observed OS-draw ranges. Proof mutation and a failed withdrawal CPI
reject with byte-exact rollback. See the frozen source/artifact/run index in
`evidence/p3-private-leaf-salts-20261013/RESULTS.json`.

These measurements establish fit for the tested paths, including rollovers;
they do not prove a uniform CU bound over all statements or a private-spend
security claim. No live program was deployed and no funds were moved. Task
keys and nonce ledgers remain retained on the NUC.

The subsequent [literal append checkpoint](APPEND-GATE-BRIDGE.md) derives
the ordered output pair, twenty append nodes, next root, and carry frontier
entry from the production gates on the same extracted R1 candidate. Its
complete-frontier result retains an explicit non-carry public-check premise.
The focused NUC import/axioms checkpoint passed with standard axioms only.
It does not close frozen-table generation, chronological tree correctness,
Rust correspondence, the shared-oracle reduction, or privacy.

The next [concrete table and tree bridge](APPEND-TREE-BRIDGE.md) closes the
frozen-table recurrence and chronological append-root equality in the Lean
field model. It retains the authenticated old-frontier invariant, handles
the final full-capacity insertion, and strengthens the same R1 candidate.
The actual stored-frontier invariant and Rust/account refinement are still
required; shared-oracle soundness and privacy are not consequences of this
deterministic root theorem.
