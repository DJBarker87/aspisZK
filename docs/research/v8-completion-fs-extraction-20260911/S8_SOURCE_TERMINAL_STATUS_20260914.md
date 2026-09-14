# S8 source cuts and ordinary terminal

Base: `6f0e9a068e616f658265ac8ba55b1df4ef22402c` on
`research/v8-completion-fs-extraction-20260911`.

This continuation advances the selected functional model.  It does not claim
global soundness, literal Rust refinement, or production readiness.

## Checked source endpoint

`FSV8S8TerminalExecutionCuts.successful_run_constructs_terminal_execution_cuts`
takes a successful execution of one terminal-checked selected script.  It
constructs, rather than accepts from the caller:

- the adversary-returned canonical body and its parsed wire;
- the successful semantic run on the same persistent oracle;
- exact before-C1, C1/lambda/chi/C2, and post-C2 interpreter segments;
- their chronological oracle-prefix relations;
- the selected suffix and its final oracle; and
- the complete ordinary terminal operands and accepted equation.

The terminal evaluator derives the q22 schedule, query records, opened values,
response0, final256, later responses, positive query increment, ordinary
weights, chord transport, four fold challenges, and sparse image term from the
same body and staged transcript.  No terminal equation, image adapter, query
adapter, target polynomial, candidate, cut, or history is a theorem input.

The execution cuts are deliberately distinct from first-creator cuts.  A
prover may have prequeried a transcript input.  Raw challenge-limb recovery
into the older `RootCuts` record is also not claimed; the checked endpoint
records the decoded lambda/chi phase and the literal runs that produced it.

## Other checked results

- `S8SemanticSegments.actual_semantic_run_factorises` proves exact run-level
  factorisation of the source semantic script into allowances 3, 134, and
  1663.  It compares complete interpreter results and final oracle states.
- `S8BufferedPotential.source_challenge_log_length_le_eight` proves the live
  buffered QM31 draw makes at most eight shared-oracle calls on success,
  cache-hit, decoder-failure, and exhaustion paths.
- `S8SemanticPathBudget.selected_semanticScript_logBound_234` proves the
  selected positive semantic script makes at most 234 shared-oracle calls on
  every path: 27 bounded candidate invocations and 18 absorbs.
- `S8CutBaseCovector.baseReference` constructs the public base covector from
  the concrete pre-alpha cut's `z`, row scales, chord, and frozen inactive
  mask table.  Its word argument remains explicit.
- `S8FourRoundFirstDrop.vanishing_discrepancy_is_listed` retains the correct
  four-round first-vanishing classification.  It rules out the disproved
  alpha0-only event shape; it is not source event inclusion.

## What remains open

The selected model still uses the guard-relaxed semantic prefix.  There is no
direct Lean evaluator for the pair-forest selected masked terminal on the
arbitrary 3x28 body claims.  Existing callback models require a recovered C1
table plus explicit helper/mask outputs and would therefore make acceptance
circular here.  The missing direct producers are the selected Poseidon,
semantic-packed, copy-on-openings, and H/G mask evaluations, together with the
typed public/transition decode and binding.  The positive-transfer lane-94
delta and transition projection are already available, but they do not replace
the missing evaluator.

The actual ordinary probability theorem is also still open.  The checked
terminal equation has not yet been connected to:

1. a received virtual quotient fixed by the actual C1/C2 answer prefixes;
2. the applicable prefix-derived quotient family and its cardinality;
3. the full covector including image and query contributions;
4. the actual residual at each of alpha0 through alpha3; and
5. the killed-sampler pushforward for fresh outputs and first-creator
   restoration for cached outputs.

Consequently the existing routed `cap / p^4` consumer still has no actual
selected-acceptance event inclusion.  The generic first-drop lemma and base
covector do not fill that source gap.

Permitted replay extraction, 116 usable continuations, recovered semantic
enforcement, checked payment extraction, full-view adaptive zero knowledge,
and global composition remain open.  The global numerical bound is therefore
undefined; conditional 103--105-bit screens are not promoted.

## Resource and format status

The proof body is unchanged at 40,282 bytes.  This continuation adds no wire
field, nonce, challenge, or protocol round.  It changes only research Lean
models and evidence.  It contains no SBF build or matched complete-transaction
CU measurement.

The 234-call theorem covers only the semantic prefix.  It does not prove the
candidate 420-call bound for the entire prefix; the suffix still needs its
source inventory of 22 further ordinary invocations and 10 absorbs.  The
inherited 3195/3262 syntax bounds remain valid coarse controls and are not
whole-verifier or extractor budgets.

## Reproduction and evidence

The supplied S8 reference suite passed 61 tests.  The final focused Lean
aggregate ran on the Tailscale NUC with Lean 4.32.0 in one systemd user scope:

```text
MemoryHigh=8G MemoryMax=9G MemorySwapMax=0 RuntimeMaxSec=600
run_s8_source_terminal_checks.sh
exit 0; wall 27.49 s; peak RSS 6,794,116 KiB; swap 0
```

Every promoted endpoint printed only `propext`, `Classical.choice`, and
`Quot.sound`.  The final aggregate compiled current sources in dependency
order; no `sorry`, `admit`, or new axiom appears in the S8 files.

The first failed aggregate invocation did not inherit `LEAN_BIN`/`LEAN_PATH`
through systemd and exited before Lean started.  The corrected invocation used
`/usr/bin/env` inside the cgroup and is the result above.

## Decision

S8 closes a real same-body ordinary-terminal/cut integration gap and a useful
source call budget.  It does not yet support a global soundness number.  The
single next decisive implementation is a prefix-derived received quotient and
bounded reference-family constructor consumed by the checked terminal's
four-round residual classification.  That is the shortest route to an actual
fresh ordinary-event probability theorem; cached restoration follows from the
same target only after its first-creator availability is proved.
