# R17 rational chord normalization

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
