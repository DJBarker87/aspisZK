# R17 G-independent correction target and coverage inventory

Date: 2026-09-21. Source base
`5abdc0119d1d39105fd8f359ec088a43c5960203` plus this changeset.

## Source dependence being removed

The witness shear requires the G translation to depend on C1/H1 and the
fixed prefix, but not on the old G coins. The staged terminal has the form

`(base + factor*g) - g*factor + g + extra = base + extra + g`.

Here base retains the entire nonlinear C1/H1 semantic composition and
ordinary mask terms. `extra` is the positive-transfer correction; it uses
C1 claims, not G. Thus comparing two contexts with the same old G cancels
old G. Changing G adds exactly its structured-mask difference.

Inspected source anchors:

- `pair_forest_semantic_terminal.rs`: `composition_parts` builds the
  openings from 16 C1 columns, mask-only terms, H1/copy and semantic lanes;
  G is returned separately. `terminal_parts` adds H1 terms. The selected
  wrapper returns `state_only_selected_mask_value + eta*original`.
  File SHA-256 `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.
- Core `state_only_hiding.rs`: explicit G enters the mask additively with
  its public factor. SHA-256
  `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`.
- Staged `payment_terminal` subtracts that old factor and adds the
  structured first G claim; staged positive-transfer residual reads C1
  claims 1, 29 and COL (COL=3), not G.

`TerminalG.lean` proves the replacement identity, G-shift identity,
old-G independence across arbitrary nonlinear base contexts, and its
Boolean-suffix consequence. It also proves additive round evaluation and
the literal reverse mask accumulator's additive identity for equal-length
contribution lists. These hold over a field without a random-challenge
premise. They are source-shaped algebra, not a complete Rust refinement.

The v18 diagnostic explicitly copies both message arrays and zeros the
entire G column for the non-G path. It computes the G contribution only
from `mixed_coins(newG) - mixed_coins(oldG)`. Thus no old G data reaches
the non-G terminal calls, including the two ordinary G point claims.
At every interpolation sample it checks this split against the literal
old/new source terminal difference. This happens both before solving G and
after applying the correction: 28*(2^10-1)*2 = 57,288 comparisons per
witness direction. No private vectors are exported.

The prefix, including eta, is fixed in this statement. In the actual
execution eta follows the G-dependent initial claim. No unconditional
independence of eta and G, or causal sampler property, is inferred here.

## What the rank problem now precisely requires

Update: `R17_OOD_PAIR_COVERAGE.md` replaces the two-row H1 OOD rank test
below with explicit distinct-point interpolation. The remaining larger
rank conditions are unchanged.

These matrices are functions of public prefix data and fixed layouts,
not of old mask values. Their affine targets may depend on the witnesses
and C1/H1 context. The G target no longer needs an assumption of old-G
independence: its candidate computation separates that dependence, with
the source correspondence checked as described above.

| Map | Candidate dimensions | Required lower rank outside exceptional set |
| --- | --- | ---: |
| C1 raw/point/OOD, each of 16 columns | 108 M31 observations on legal free mask cells | 108 each |
| H1 first OOD correction | 2 QM31 observations on 809 balanced inactive directions | 2 |
| H1 joint correction | 562 equations on 1022 OOD-zero quotient coordinates | 540 |
| G semantic/view/relation correction | 625 equations on 1022 OOD-zero quotient coordinates | 601 |

The known 22 H1 and 24 G compatibility equations supply candidate upper
bounds. Actual-prefix rank and affine-target tests do not prove the lower
bounds for every source query schedule or bound the exceptional probability.
Gamma only rescales the relevant nonzero channel targets; omitting its
powers is still incorrect. H1/G point constraints, source OOD/chord
conditions, first-relation alpha and the post-Final512 query schedule must
remain joint, not separately conditioned without justification.

**First remaining proposition:** establish these compatible-image lower
bounds and target consistency for arbitrary eligible source prefixes,
outside an explicitly bounded exceptional set, including all permitted
query schedules. A nonzero minor at one schedule does not certify another.
The retained adaptive-prefix, commitment-hop, seed, failure/publication
and soundness obligations remain open. No global privacy theorem follows
from this dependency result.

## Focused evidence

Lean used `/Users/dominic/ZK/AspisFormal`, its existing cache and
`lake env lean -j1 -M1800`, with local r17/r16 object paths prepended.
The first attempt failed only because the induction hypothesis arguments
were supplied in the wrong order. Named arguments fixed the proof with
no statement change. The failed log's elaboration `sorryAx` is not proof
evidence. The final six declarations use only subsets of propext,
Classical.choice and Quot.sound; the accepted axioms audit has no sorryAx.

Rust used the retained release host cache with offline/locked/jobs=1 and
the exact flags/features in the stage manifest. v17 compiled but was
superseded before runtime: it zeroed the structured G coins but retained
the two ordinary G point inputs. v18 zeros the entire G column for the
non-G path. This strengthens the data-flow separation without changing
the target identity.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| TerminalG.lean initial argument-order failure | 1 | 10.86 | 1672445952 | 0 |
| TerminalG.lean corrected | 0 | 10.70 | 1691451392 | 0 |
| v17 host build, superseded before runtime | 0 | 50.38 | 738787328 | 0 |
| v18 host build | 0 | 48.46 | 738557952 | 0 |
| v18 world0, 57,288 split comparisons | 0 | 34.69 | 287637504 | 0 |
| v18 world1, 57,288 split comparisons | 0 | 34.43 | 287866880 | 0 |

Both runs select the honest fixture, `ASPIS_R17_C1_WITNESS_AUDIT=1`,
`NO_DNA=1` and `ASPIS_R16_SELECTED_SECOND=0`/`1`, with live/complete
contexts and oracle/nonce/scan overrides unset. All preceding C1/H1/G
correction and initial-claim assertions pass. Original proof hashes remain
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`;
unchanged proof bytes show diagnostic transparency, not privacy.

All metrics are from `/usr/bin/time -l`. Logs under
`/tmp/aspis-r15-host.drHYn9`: `r17-terminal-g-lean.log` (failed),
`r17-terminal-g-lean-v2.log`, `r17-build-v17.log`, `r17-build-v18.log`,
and `r17-v18-world0.log`/`r17-v18-world1.log`.
The final stage is `r17-two-channel-source-v18`; manifest SHA-256
`112f81f72c24773d5239ca7eb1e89a8a9bd1fe62f9039df0ec6b72de1539a4e0`.
No production paths or negative regressions changed. This is not a full
manifest/release replay or a universal source theorem.
