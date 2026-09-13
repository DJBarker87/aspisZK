# Current V8 privacy-repair status

Date: 2026-09-13.

Status: **R7 Tickets A/B complete conditionally; Ticket C stops at the paired
C1/C2 commitment kernel; no full-view privacy repair or production release
claim**.

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
`COMPATIBILITY_DIFF.md`, and
`REMAINING_OBLIGATIONS.md` for the exact handoff. No deployment, transaction,
wallet/key operation, force push, merge, SBF build, Aeneas replay or full
generated-certificate aggregation was performed.
