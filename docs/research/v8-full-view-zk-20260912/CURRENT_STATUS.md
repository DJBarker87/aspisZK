# Current V8 privacy-repair status

## Latest source-block binding — 2026-09-21

All 392 diagonal-block entries now have compiled equalities to the
assembled weighted finite source model, generated from the frozen indices
in 13 bounded chunks. Regeneration and all axioms audits pass. Next is
the off-diagonal zero pattern, permutation and determinant composition.
This is not a full privacy/soundness theorem; see `R17_MINOR_BLOCKS.md`.

## Latest certificate preflight — small blocks, 2026-09-21

The fixed minor's challenge-independent support decomposes into 60 1x1,
65 2x2 and 8 3x3 blocks. Exact source tests verify the triangular ordering
and all diagonal block ranks at the fixed witness. `R17_MINOR_BLOCKS.md`
records the resulting small-block formal certificate route. Frozen block
data now matches the source exactly (133 blocks, 29 distinct evaluated
matrices). All 29 small determinant leaves now compile with a passing
regeneration check. Formal source-block binding and determinant composition
remain next; the generic two-block, row-permutation and evaluated-nonzero
composition gates now compile under the existing cap. No global security
gate is closed. The 214 active source row/coefficient mappings are now
frozen and checked exactly; formal sparse-unit-column binding remains.
The sparse unit-column and subsequent sparse-scatter evaluation lemmas
now compile, enabling bounded source-block certificate generation.
Both chord-unit parity formulas, including sparse x², now also compile.

## Latest polynomial bridge — 2026-09-21

`sourceEntry_eval` and `sourceEntry_degree` now compile: the polynomial
built from the assembled weighted finite chord model evaluates exactly
to its coefficient and has total degree <=5. Next is the fixed matrix/minor
instantiation with a kernel-checked nonzero witness. Concrete Rust
representation refinement and adaptive probability remain open; this is
not a full privacy or soundness theorem. See `R17_ACTIVE_MINOR.md`.

## Latest coverage step — fixed active minor, 2026-09-21

`R17_ACTIVE_MINOR.md` records a fixed 214-column nonvanishing witness at
alpha=2,u=3,v=4, with independent inverse-product verification and frozen
column indices. The degree argument gives (642,214,214) separate bounds,
and the generic determinant total/per-variable degree lemmas now compile,
as does total degree <=5 for the six-constant active-entry normal form,
and its generic linear-functional identity. All 149586 source entries
match that reconstruction at the fixed witness,
and the source-shaped scatter loop has a compiled linearity proof plus
1025 passing basis checks at both chord-multiplication input lengths,
with both parity formulas now composed into a universal source-shaped
six-constant theorem,
and compiled zero-extension/parity/bounded-output boundary lemmas,
now composed through the finite 512/513/514-length chord reads,
with kernel-checked success/index bounds for all 512 and 513 source columns,
and a universal repeated-weight-to-power correspondence,
now assembled into the chord theorem and composed with non-pivot inverse
transport,
but a compiled polynomial/source bridge and actual adaptive probability
law remain open. The algebraic evaluation is not an accepted OOD draw.
No global privacy or soundness conclusion follows from this certificate.

## Latest algebra step — normalized chord, 2026-09-21

`R17_NORMALIZED_CHORD.md` records a compiled rational-chord identity and
nonzero-scale theorem with explicit denominator/distinctness premises.
Parameter recovery and injectivity now also compile; both retained source
prefixes pass recovery through the actual OOD function and chord equality.
Source parameter binding, a fixed active minor/degree certificate and
the adaptive sampler law remain necessary before a loss bound. This is
not a full privacy or soundness result.

## Latest coverage step — active/query separation, 2026-09-21

`R17_ACTIVE_QUERY_SEPARATION.md` records fixed source geometry: active
coefficients start at 100, while the low raw/final correction ends at 90.
All 264 low quotient/chord basis checks pass. The direct active map uses
only alpha, chord and layout; it and the factored map have rank 214 at
both prefixes. Next is a universal minor/exceptional-event argument for
that direct map, then the remaining point/G constraints. This is not a
full privacy or soundness result.

## Latest coverage step — balanced kernel, 2026-09-21

`R17_BALANCED_KERNEL.md` records the compiled nonzero secant-normal
theorem and the image/balance equivalence. Source checks identify 699
balanced kernel directions and one explicit balance direction. Both
prefixes pass the remaining H1 rank 217 and G rank 278 checks. Universal
coverage of those residual maps, adaptive loss accounting and full
privacy/soundness remain open.

## Latest coverage step — factored kernel, 2026-09-21

`R17_RAW_FINAL_KERNEL.md` records the compiled vanishing-polynomial
characterization of raw-zero/final-zero corrections. A source-basis test
constructs 700 independent quotient directions without dense nullspace
elimination. At both actual prefixes, the remaining H1 map has rank 218
and the G map rank 279 (281 rows with two compatibility equations).
Universal coverage of these residual maps is the next source obligation;
global privacy, exceptional-event accounting and soundness remain open.

## Latest coverage step — raw/final compatible image, 2026-09-21

`R17_RAW_FINAL_COVERAGE.md` records a compiled interpolation theorem for
every distinct-fibre schedule and every alpha: all compatible raw/final
targets have a quotient construction. Source tests pass at both accepted
prefixes with three alpha cases each. A new negative control explicitly
shows this construction does not enforce H1 active-row legality. Next is
the raw-zero/final-zero kernel and coverage of the remaining H1/G
constraints there. No full privacy or soundness result is claimed.

## Latest coverage step — explicit two-OOD correction, 2026-09-21

`R17_OOD_PAIR_COVERAGE.md` replaces the H1 two-row rank test with an
explicit constant-plus-x/y pad. Lean proves interpolation for every
distinct point pair. Both source coordinate branches, coincident-point
rejection and both complete witness-change diagnostics pass. This removes
the extra algebraic rank exception from that small step; the sampler's
failure branch, C1/H1-joint/G coverage and global privacy/soundness remain
separate open obligations.

## Latest source dependency — G-independent target, 2026-09-21

`R17_G_INDEPENDENCE.md` records compiled source-shaped algebra and 57,288
literal-versus-G-separated terminal comparisons per witness direction.
Both actual-prefix runs pass, retaining the previous joint corrections.
The non-G path receives an entirely zeroed G column. This supports the
fixed-prefix triangular transport dependency, not independence through
eta/commitment sampling. Universal rank/compatible-image bounds and the
adaptive full-transcript source argument remain open.

## Latest proof step — three-block transport, 2026-09-21

`R17_WITNESS_TRANSPORT.md` records two compiled leaves: the invertible
C1/H1/G triangular coin transport and the separate two-sided prefix
invariant needed to select a transport adaptively. A Boolean counterexample
formally prevents inferring adaptive bijectivity from fixed-prefix
bijectivity alone. Final axioms audits contain no sorryAx. Universal
source correction identities, exceptional-event bounds, seed law and
commitment/oracle chronology remain open; no global privacy claim.

## Latest witness step — semantic/G compensation, 2026-09-21

`R17_G_WITNESS_JOINT.md` records both actual-prefix witness changes:
625 G equations pass (rank 601), all 271 semantic coordinates and seven
first-relation coefficients cancel, and the retained G view is unchanged.
The full source terminal is re-evaluated across all ten rounds after
correction. A caught false initial-zero assumption is retained in the
ledger; the corrected diagnostic checks the initial affine target against
the source builder and restores the actual original claim. Next is
universal compatible-image coverage with bounded exceptional events and
source-grounded distributional/oracle composition. No full privacy or
soundness claim follows from these two fixtures.

## Latest witness step — joint H1 correction, 2026-09-21

`R17_H1_WITNESS_JOINT.md` records successful affine corrections in both
actual fixture prefixes. All 562 original equations hold (rank 540),
retaining H1 raw/point/OOD values and cancelling the combined C1/H1
rest-channel Final256 offset. The actual encoder, OOD/MLE and padding
routines independently check the result. Next is G compensation for the
full changed-context semantic and first-relation differences. This is not
yet a complete fixed-prefix witness coupling, much less full privacy or
soundness preservation.

## Latest affine helper step — OOD correction, 2026-09-20

The v12 diagnostic constructs a legal H1 pad cancelling the rebuilt
witness-helper difference at both OOD points, in both actual fixture
prefixes. Rank is 2 over 809 legal directions; original equations and the
actual padding/OOD routines pass. Active helper offsets are retained.
This is only the first affine helper step: joint raw/point/rest-Final256
correction, semantic compensation and adaptive full-transcript arguments
remain open. See the v12 evidence in `R17_C1_WITNESS_CHANGE.md`.

## Latest witness step — C1 affine correction, 2026-09-20

`R17_C1_WITNESS_CHANGE.md` records an actual opposite-witness correction
preserving C1 raw/point/OOD observations at both source prefixes. The
corrected trace passes the witness/compiler validator. Rebuilding H1
changes two rows; that offset is retained for the next correction.
C2, semantic and final/relation observations are not yet coupled across
witnesses. Full privacy and soundness preservation remain unproved.

## Latest construction — coupled invisible correction, 2026-09-20

`R17_COUPLED_CORRECTION.md` records an explicit nontrivial H1/G correction
at both source prefixes. All 271 semantic effects and seven gamma-scaled
relation coefficients cancel; retained views and direct source encoder/OOD
checks pass. This is within-context remasking, not a witness-change coupling
or a claim that commitment roots stay fixed. Full privacy remains open.

## Latest source step — H1 semantic map, 2026-09-20

`R17_SOURCE_H1_SEMANTIC_MAP.md` records the constructed 271-by-1024 H1
coordinate map using the selected terminal and interpolation. Both real
contexts pass every terminal-basis check and all 809 legal-pad initial
checks; their proof bytes remain identical. The internal map is not
published. Constructing the full context-dependent correction and proving
adaptive/full-transcript privacy remain open.

## Latest step — posterior counting, 2026-09-20

`R17_POSTERIOR_COUNTING.md` records compiled fiber-count/uniform-law
lemmas and a reversible context-dependent correction allowing different
hidden H1 semantic maps. H1 coverage is now checked at both real prefixes
(325/347). Source construction of those semantic maps/corrections and the
adaptive commitment/oracle/seed argument remain open; no full privacy claim.

## Latest step — explicit joint compatibility, 2026-09-20

`R17_JOINT_COMPOSITION_BOUNDARY.md` retains the serialized first G point
and checks rank 601/625 at both actual prefixes, accounting for 24 equations.
A conditional compatible-image composition lemma and the exact source-shaped
H1 affine terminal identity compile. The source H1 semantic-coordinate map,
its compatibility laws and the adaptive posterior argument remain open.

## Latest diagnostic — actual R17 verifier prefixes, 2026-09-20

`R17_ACTUAL_PREFIX_COVERAGE.md` records rank 601/624 at both retained
proofs' actual verifier-derived challenges and queries. Public-only audit
records are checked in; synthetic negatives remain. This closes neither
the joint H1/G composition nor adaptive exceptional-event accounting.

## Latest proof step — R17 source-shaped algebra, 2026-09-20

`R17_SOURCE_ALGEBRA.md` records two compiled Lean leaves. The literal
reverse mask accumulator equals the existing structured-cube recurrence,
including its full sum and next suffix polynomial. The channel identities
now retain arbitrary false-claim and quotient residuals without assuming
honest inputs. Concrete Rust field/index/packed-column refinement remains
open, as do the joint adaptive privacy and soundness arguments.

## Latest step — R17 staged source integration, 2026-09-20

`R17_SOURCE_INTEGRATION.md` records a compiled, domain-separated research
host with structured G, two quotient channels and Final512. Two different
witnesses with identical public inputs produce accepted proofs; dense and
deferred verification agree, with retained/extended rejection controls.
The earlier arithmetic-only boundary below is historical. Production paths
remain unchanged; this is neither full privacy nor a soundness proof.
Next: universal source refinement of the structured semantic computations
and two-functional committed-column relation, then joint causal posterior
composition and adaptive oracle/seed/failure/publication loss accounting.

## Latest step — R17 two-channel arithmetic, 2026-09-20

`R17_TWO_CHANNEL_OPENING.md` records the implemented test-only opening
arithmetic: two OOD interpolants/quotients, separate functionals and image
gates, Final512, 44 raw/final checks with disjoint query-injection powers,
and four relation rounds. Fixed-fixture checks give H1 rank 325 of 347
after legal-pad/OOD constraints, and G rank 601 of 624 including the first
relation polynomial. Prior negatives remain intact.

Lean proves the two-channel pullback for the additive R16 transform and
conditional root-count bounds that include ordinary/carried claim errors.
No new source wire profile or full-transcript theorem exists yet. Next is
matched prover/verifier integration in a separate research stage, followed
by the joint causal/source/oracle and exceptional-event obligations.

## Latest candidate check — R17 mixed mask, 2026-09-20

`R17_MIXED_MASK_BOUNDARY.md` records a prototype using invertible public
mixing of existing G coins. Five focused Lean leaves compile: mixing,
round coefficients/degree/boundary, causal cuts, Boolean-cube recurrence,
and the shared-functional limitation. Its fixed joint map reaches rank 596
of 618 and the ten-round algebra test passes. This is not a source profile.

Source inspection identifies the next integration obligation: the existing
single-quotient PCS uses one shared functional, whereas structured G needs
a different one. A negative regression and abstract theorem prohibit the
naive substitution. A two-channel opening route is specified for scrutiny,
not implemented. Its extra disclosures and adaptive rank/loss proof must
be established before any full privacy or soundness claim.

## Retained first-placement negative — R17

`R17_STRUCTURED_G_CANDIDATE.md` derives a proposed ten-round zero-boundary
G mask, but rejects its naive first-271-entry placement: the joint fixed
PCS map has rank 540 rather than 596, leaving 56 extra constraints.
This is retained as a passing negative regression, alongside the unchanged
R16 rank-408 requirement. No new source protocol is implemented. The next
obligation is a justified round-coordinate extraction with sufficient joint
posterior freedom; full privacy and soundness preservation remain unproved.

## Active repair direction — R16

The new user goal prioritizes an implemented repair and full privacy proof,
not further attack-frequency measurement. `R16_BASIS_REPAIR_DESIGN.md`
specifies a reversible public encoding-basis transport using existing legal
balanced C1 masks. Four focused candidate tests pass, including full raw rank
88 on the retained bad q22 schedule and QM31 inverse-dual/batching checks.
It is integrated only in a separately staged research host, not production,
and is not yet proved for the joint transcript.
`R16_UNIVERSAL_RAW_ARGUMENT.md` adds a compiled arbitrary-fibre polynomial
interpolation theorem and exhaustive source-factor/root checks. The
natural-basis endpoint now compiles for every distinct-fibre schedule.
Exact source mask/transport correspondence and joint posterior remain open.
`R16_BALANCED_TRANSPORT_PROOF.md` adds compiled balanced-lift and two-sided
inverse theorems for the source-shaped transport, with standard axioms only;
this is not yet a complete Rust refinement or distributional proof.
`R16_SOURCE_INTEGRATION.md` records the common C1/C2 transport, inverse-dual
verifier, profile binding, retained integration failures and runtime results;
global joint-view privacy and soundness preservation remain unproved.
`R16_JOINT_LINEAR_DIAGNOSTIC.md` records rank 108 for a fixed same-coin
raw/point/OOD subview in all 16 witness columns, plus the 89-pad negative
control. This excludes semantic/helper correlations and Final256 and is
not a full-transcript theorem. `R16_SOUNDNESS_OBLIGATIONS.md` separately
lists the source extraction, functional, quotient and Fiat–Shamir gates.
`R16_G_POSTERIOR_DIAGNOSTIC.md` adds a verified rank-175 correction matrix
for the first three G cuts jointly with later raw/point/OOD values at fixed
challenges. It preserves the earlier 82 coordinates when correcting the
later 93, but excludes Final256 and later semantic rounds; the R14 G-only
final-round obstruction and source commitment/oracle premises remain open.
`R16_FINAL256_CONSISTENCY.md` proves the normalized fold identity and checks
the two actual source maps on all 1024 basis units at the retained schedule.
Final256 must satisfy raw-opening consistency; the next coverage target is
the compatible joint image, not arbitrary independent final coefficients.
`R16_FINAL_POSTERIOR_DIAGNOSTIC.md` now checks that compatible image at a
fixed prefix: 430 observations including Final256 and the inactive claim
have rank 408, exactly accounting for 22 verified fold relations. Later
semantic rounds, nonlinear C1/H1 coupling and the source probability law
remain outside this diagnostic.
`R16_H1_REMASKING_BOUNDARY.md` distinguishes legal C1 remasking from a
witness change: the complete registry-input/mask-cell intersection is empty,
so remasking alone leaves unpadded H1 fixed at fixed challenges. Witness
changes still require the R7 nonlinear incidence offset; nonlinear semantic
composition and actual oracle coupling remain open.
The earlier R15 probability investigation is retained, not the current priority.

## Current verdict — 2026-09-19

**Full-transcript privacy is not established.** A literal raw C1 separator
remains; neither commitment hiding nor early-message surjectivity eliminates
plaintext disclosure. No source-valid numerical distinguishing advantage has
yet been derived from its ideal schedule probability.

See `REPAIR_DECISION.md` for the plain-language verdict and necessary repair
constraint: helper-only/early-message fixes do not remove the raw C1
separator on a published revealing schedule. No sufficient repair is proved.

R15 recovered the exact selected v4 performance source (`5ded…08d456`) from
the retained generator plus one hash-authenticated deletion of an obsolete
pre-rebind assertion. The missing host image is **no longer** the first
blocker. The deterministic demo is still not the intended entropy-backed
adapter, and three other generated preimages remain unavailable.

New focused evidence:

- `r15-circle-domain-evidence.md`: all 262,144 actual log-20 query fibres
  pass independent integer circle/composition checks. This is exhaustive
  finite executable evidence, not a Rust semantics or privacy theorem.
- `r15-exact-tower-chord-evidence.md`: the chord theorem is instantiated in
  the literal QM31 tower, with the source OOD policy's algebraic premises.
  Rust operation/query-point refinement and probability obligations remain.
- `r15-post-query-pole-boundary.md`: authenticated pre-query interpolation
  checks cover only 256 fibres. Lean now proves chord nonvanishing at every
  subfield circle point for distinct finite OOD parameters outside that
  subfield; actual-source, full-domain instantiation remains open.
- `r15-query-address-evidence.md`: the SHA fixture's first query addresses
  are fresh in the observed callback history; read-only instrumentation
  preserves its complete proof bytes. Universal freshness and publication
  probability remain unproved.
- `r15-complete-host-disclosure-evidence.md`: the recovered host builds and
  produces an accepted complete proof in synthetic account mode. Two
  source-derived controlled same-public executions under one fixed six-cell
  function produce accepted proofs with raw statistic difference 490597912.
  This is not the intended random-oracle event-probability theorem.
- `r15-universal-disclosure-evidence.md`: Lean zero-extension theorem for
  every containing injective schedule, with the literal certificate scalars;
  authenticated fixed-witness demo boundary and correction of the older
  source-advantage overclaim.
- `r15-q22-source-slice-audit.md`: exact initial/v4 image recovery, disabled
  stress mode, and separate positive/negative proof-file sinks.
- `r15-q22-stopping-evidence.md`: three actual sampler tests, including the
  extra block consumed at boundary success; exact 64-word IID event counts,
  explicitly not an actual oracle/publication law.
- `r15-r12-terminal-inverse-evidence.md`: 56 complete selected-terminal
  target checks at cuts 1 and 2, preserving the earlier fixture observations.
  This is not a universal source equivalence or public-only simulator.

The first source proposition is the entropy-backed attempt's joint
shared-oracle, query/stopping, and public-event refinement. Independent
positive obligations remain: universal source coefficient identities and
three-cut inverse; actual paired-commitment/seed first-hit instantiation;
and continuation through all remaining semantic rounds, 87 point fields,
OOD, Final256, openings and visible failures using the retained posterior.
Do not restart the H1-only schedule search.

## Historical R8 status — retained, not the current next-step prescription

Date: 2026-09-13.

Status: **R8 universal witness-retaining paired-commitment hop and ideal salt
counting proved; source refinement and public algebraic provider remain open;
no full-view privacy repair or production release claim**.

## Milestone ledger

| Milestone | Result | Remaining blocker |
|---|---|---|
| R0 source lock | PASS for manifest, pins and source-locked negative regressions | Complete generated profile remains partial: 3/10 transformation preimages unavailable |
| R1 joint model | MODEL BOUNDARY COMPLETE | No universal difference basis, complete 697-QM31 joint adapter, or reconciliation of 84 internal versus 87 serialized point fields |
| R2 raw affine gate | PASS as exact raw certifier; known spread schedule covers and q4/q6 schedule separates | Raw linear coverage is not chronological full-view coverage |
| R3 simulator | PASS for the fixed affine public-coset theorem and Rust construction | No public causal H1/C2 law, joint V8 quotient, or full simulator |
| R4 publication | PASS as immutable fail-closed research boundary | It deliberately issues no permit and is not wired into production |
| R5 retry/loss | PASS for generic release transport and non-IID retry bound | No positive source-specific release lower bound and no assigned global loss |
| R6 handoff | OUTCOME (b) | First nonlinear H1/C2 causal-coupling theorem is the exact next obligation |
| R7 Ticket A | PASS: literal source gives `H1_unpadded = D a` under honest validation and pole freedom; 1024-row fixture delta matches | The source identity alone is not privacy |
| R7 Ticket B | PASS: actual-encoder coverage and coordinatewise C2 lift; conditional Lean fixed-observation theorem | Fresh conditional pad law is a separate prefix/commitment premise |
| R7 Ticket C | PRECISE BOUNDARY | Causal paired C1/C2 same-salt commitment kernel in one coherent lazy random oracle, before first semantic message |
| R8 finite commitment hop | PASS, SAME-PROVIDER | Both exact marginals, forward execution invariant, atomic paired materialization, and event gap bounded by Bad; witness retained |
| R8 ideal salt loss | PASS, CONDITIONAL ON FIBER CAP | Adaptive coordinate counting and duplicate-salt union bound; actual seed hybrid and source query cap open |
| R8 selected grammar | PASS, LOCAL SOURCE EXACT | 403/186-byte packed payloads, 32-byte shared salt, 0x71/0xf1 leaf tags, 53-byte parents; complete SHA-call-trace refinement open |

## Decisive evidence

The actual encoder reproduces the q4/q6 separator on a same-public valid
duplicate-input witness pair, and actual mask application preserves its
nonzero delta. Exact Rust certification also shows this is schedule dependent:
a fixed spread 22-query schedule has raw rank 88 for all 16 columns, while the
scattered schedule containing fibres 4 and 6 has rank 86. This is raw
diagnostic evidence, not a full-view simulator or a Fiat--Shamir probability.

R7 removes the overly broad “nonlinear H1” obstruction. Honest validation
enforces equality of all 16 producer/consumer tuple limbs on each active copy
link. Away from explicit poles, the unpadded helper is therefore a public
136-edge incidence combination `D a`, even though its coefficients are
nonlinear. The 809 inactive-row pad directions cover the tested fixed H1
observations under the actual encoder, and the supplied Lean transport proves
the corresponding conditional fixed-observation law.

The selected chronological source still commits pad-dependent H1 in C2 before
the first semantic message, using the same per-leaf salt as C1. The first
selected semantic message is affine in the remaining H1 pad after prior state,
challenges and coins are fixed; it is not the first blocker. The exact blocker
is a causal paired C1/C2 same-salt commitment kernel preserving the prior C1
root and coherent random-oracle history and supporting later adaptive q22
openings. Existing fixed-query paired-salt hiding does not provide that kernel.

The research publication boundary consequently returns
`CompleteFullViewCoverageUnsupported`. Its release probability is zero and
its finite-cap exhaustion probability is one. Retrying unsupported coverage
does not repair it. All symbolic seed, salt, commitment, algebraic, oracle,
sampler, stopping, visible-attempt and source-refinement losses remain
explicit; none is silently assigned zero.

## What is and is not established

Established: source-locked regressions; the source-instantiated conditional
H1 incidence identity; exact actual-encoder H1 fixed-observation corrections;
coordinatewise C2 encoding; the conditional Lean helper-observation theorem;
exact 84/87 projection accounting; exact affine correction/separator
certification; a fixed-affine public-coset simulator; immutable fail-closed
publication enforcement shape; generic release-event transport and
conditional retry-failure mathematics.

Not established: the ideal-expander/fresh-pad prefix law; a causal paired
C1/C2 salted-commitment kernel; transport of the semantic and later transcript;
complete generated-source reconstruction; complete joint V8 source map;
public quotient; adaptive random-oracle simulator; useful publication permit;
positive release bound; source-to-model refinement; independent final replay;
or any global V8 privacy advantage bound.

See `R7_H1_C2_INCIDENCE.md`, `R7_FIRST_SEMANTIC_BOUNDARY.md`,
`R8_PAIRED_COMMITMENT_HOP.md`, `R8_EVIDENCE_LEDGER.json`,
`COMPATIBILITY_DIFF.md`, and
`REMAINING_OBLIGATIONS.md` for the exact handoff. No deployment, transaction,
wallet/key operation, force push, merge, SBF build, Aeneas replay or full
generated-certificate aggregation was performed.
