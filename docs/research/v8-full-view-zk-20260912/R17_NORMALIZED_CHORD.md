# R17 rational chord normalization

## Parameter recovery extension

On base `749918c1` plus the extension changeset, Lean additionally proves
`rational_parameter_recovery` and `rational_parameter_injective`: under
the explicit nonzero denominator and characteristic-not-two hypotheses,
`1+x(u)` is nonzero, `y(u)/(1+x(u))=u`, and equal coordinate pairs imply
equal parameters. The same focused command below passed: exit 0, wall
8.35 seconds, peak RSS 1,361,543,168 bytes, swaps 0. All four printed
theorems use only `[propext, Classical.choice, Quot.sound]`; four harmless
tactic-style warnings remain.

Inspection of `crates/aspis-core/src/circle.rs` confirms the implemented
map uses these rational formulas, explicitly rejects a zero denominator
via `try_inv`, then rejects parameters in CM31 for the OOD policy.
This inspection is not a machine-checked Rust-to-Lean refinement.

The new research-only test `r17_actual_prefix_normalized_chord` recovers
both parameters from each retained prefix, checks nonzero denominators,
calls the actual `secure_ood_circle_point_from_parameter` and requires
exact coordinate equality, checks parameter distinctness and nonzero
chord scale, then compares all three chord coefficients. Both retained
worlds pass (one test each, zero failures). Commands use
`cargo test --offline --locked --release --jobs 1 -p aspis-prover --lib
r17_actual_prefix_normalized_chord -- --ignored --nocapture`, with
`ASPIS_R17_PUBLIC_PREFIX_LOG` selecting the respective checked-in record.
Measured by `/usr/bin/time -l`: world0 exit 0, 24.08 seconds,
562,905,088 bytes peak RSS; world1 exit 0, 0.23 seconds, 81,264,640 bytes.
Both report zero swaps. World1 output is retained at
`/tmp/aspis-r15-host.drHYn9/r17-normalized-chord-world1.log`; world0 and
Lean output were returned directly by the command tool.

The first remaining coverage obligation is a fixed nonzero active minor
with a degree certificate. General source/sampler correspondence and
adaptive probability accounting remain separate from these two-prefix
checks. No production source, negative regression or hiding premise changed.

Date: 2026-09-21. Source base: `4330ae8dbc11040d9655b0f511bca4dc4c21ce0e`
plus this changeset.

`lean/AspisV8R17/NormalizedChord.lean` proves, over any field, the three
chord identities for rational circle coordinates
`x(u)=(1-u²)/(1+u²)` and `y(u)=2u/(1+u²)`:

`[x(u)y(v)-y(u)x(v), y(u)-y(v), x(v)-x(u)]`
equals `2(v-u)/((1+u²)(1+v²)) * [1+uv, uv-1, -(u+v)]`.

The scale is proved nonzero when characteristic is not two, both
denominators are nonzero, and the parameters are distinct. All conditions
are explicit; this file does not assert their source discharge or a
distribution for the parameters. No new cryptographic assumption is used.

This removes the rational algebra step from the proposed direct-active-map
minor argument. Next obligations are to bind the retained source OOD
parameters to these definitions and premises, certify a fixed nonzero
active minor and its degree, and justify the actual adaptive sampler law
before assigning a loss bound. Other C1/H1/G coverage and full-transcript
privacy and malicious-prover soundness obligations remain open.

## Focused compilation

From `/Users/dominic/ZK/AspisFormal`, using the existing cached workspace:

`/usr/bin/time -l lake env lean -j1 -M1800 /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/NormalizedChord.lean`

Exit 0; wall 8.77 seconds; peak RSS 1,358,430,208 bytes; swaps 0.
Both `rational_chord_normalization` and `chordScale_ne_zero` report exactly
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.
Three non-failing tactic-style linter warnings were emitted. No Rust or
production source changed, no full suite reran, and no source test or
source-refinement theorem is claimed by this compilation.
