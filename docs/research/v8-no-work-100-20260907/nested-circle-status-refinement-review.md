# Detailed nested-circle status refinement

`experiments/NestedCircleStatusRefinement.lean` is checked, NUC v2, exit 0:
fourteen declarations and fourteen standard-only axiom audits. It imports
only the newly checked `NestedCircleSourceRefinement`. No old leaf or cache
boundary was changed.

## Checked deterministic endpoint

The leaf proves four concrete prerequisites for a one-block continuation
interpreter, all over the actual status and decoder definitions:

- `ordinary_strict_prefix_needMore`: every strictly shorter block cut of an
  actual successful ordinary call is genuinely short input. It is not a
  hard failure or impossible layout failure hidden by Option.
- `ordinary_next_accept_empty`: if the previous pending prefix needs more
  input and appending one actual block succeeds, then `blocksUsed` equals
  the entire enlarged prefix length and `remainingBlocks=[]`. This is the
  precise fact needed before `afterOrdinary` may reset pending to empty.
- `ordinary_hard_failure_append`: a hard failure cannot be repaired by
  later input. The controller must abort immediately, not start another
  inner or outer attempt.
- `ordinary_four_blocks_decisive`: at least four complete blocks imply
  either acceptance or hard failure. Neither short-input nor layout status
  remains possible; the controller's incomplete-at-four/layout branches
  can therefore be excluded on reachable source inputs.

The intermediate proofs use induction on symbolic limb fuel/count,
successful decoder extension, and the pinned V7 word-accounting bounds.
`needMore` implies fewer words than the bounded capacity. The ordinary
layout guard follows from four accepted limbs, at most 32 attempted words,
and the actual eight-word block length. No finite field is enumerated and
no claim of an honestly generated or expected tape is used.

## Scope and next consumer

These are conditional deterministic facts about literal calls, not
assumptions that verifier acceptance supplies their premises. The next
consumer is a continuation interpreter for each controller state with
`pending ++ unread` input. One-block interpretation preservation can then
be iterated to connect first circle3 and distinct3(circle3) on the exact
returned suffix. The whole-run theorem is deliberately separate and not
claimed in this leaf.

No fixed disjoint four-block windows, source reads after hard abort, sampler
mass, random-oracle freshness, or Fiat–Shamir law is inferred. Unvisited
named slots can only be ghost-filled after the source run halts.

## Provenance and focused checks

Working parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.
Borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Direct imported locality source SHA:
`8e4afcb38782a6eeb2736c66e74e533c81bfcc0c59b7d48854101198d70c2945`;
green olean SHA:
`1836391d1daff359c10cf6814133a97ca57ac91dfebd2d2b83441783cb044550`.
All further imports are in its verified cached closure. Both attempts ran
under explicit serialized NUC grants, through Tailscale numeric IP
`100.108.41.90`, with the inherited 8 GiB high / 10 GiB max / zero-swap /
CPU quota 200% scope. No other user build scope was live at preflight;
43 GiB was available. No cold dependency build or new import staging ran.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 2.98 | 6646004 | 0 | Eleven standard-only audits; only the ordinary no-layout proof needed explicit cons-list length normalization, with two dependent audits inheriting its failure. |
| v2 | 0 | 3.05 | 6678708 | 0 | One-line normalization fixed that goal; all fourteen audits standard-only. |

Exact `.log`, `-source.txt`, and `-manifest.json` files for both attempts are
retained under `experiments/nested-circle-status-refinement-nuc-vN`. The
v1 temporary `sorryAx` entries are diagnostic only, not release evidence;
v2 contains none. The final source matches its v2 snapshot byte-for-byte.
The successful postflight verifies 879 entries and records unchanged
provenance. The compiler slot was released after the terminal successful
postflight; only evidence copying/report edits followed.

The inherited scope parent is
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the working source
parent above. The retained logs give the exact Lean 4.32.0 command with
`-j1 -M9500`, target `NestedCircleStatusRefinement`, and
`run_higher_y_nuc.sh`. Native package artifacts remain a pinned-revision
cache boundary, not a package replay.

Final SHA-256:

- Source/snapshot: `4864d2cda4e7ec3196d2c4ca4b084e17a59e66c9ab4800e4747bc8612d2f3c21`.
- Olean: `637eeb7721c1b77841feb5de21f597418476b14cf3a3c990e249e000d7a297c7`.
- Log: `6e9ec03a993b90de1bf7ce27d8d39953c9f2736e45bbf69167b3cec43a7c797a`.
- Manifest: `9963e355a2cdfb618a2173042489a65338ec85abef880112f04f78d3f85ca08c`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
