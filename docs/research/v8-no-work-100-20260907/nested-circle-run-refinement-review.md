# Whole finite-tape nested-circle source refinement

`experiments/NestedCircleRunRefinement.lean` is checked, NUC v2, exit 0,
with eighteen standard-only axiom audits. It imports only the frozen
`NestedCircleStatusRefinement`; no imported artifact was changed.

## Checked exact endpoint

`sourcePair circleMap tape` is a literal wrapper: call the existing
`decodeSecureCirclePrefix circleMap 3 tape`, map its successful parameter
to the first point, call the existing `decodeDistinctPrefix` with three
outer attempts on that result's actual `remainingBlocks`, and map the final
parameter to the second point. Every `none` remains immediate failure.
The supplied map is arbitrary but fixed and purely functional; no expected
successful points or accepted source trace are assumed.

`source_pair_refines` equates this literal pair result to the
accepted-result projection of the existing block controller, started at
`.first 0 []`, folded over the same finite chronological tape. The
`accepted_iff` corollary gives equality of both points. The abort corollary
states that every controller abort entails literal source `none`.

For short input, `none` may instead correspond to a still-waiting controller.
The leaf does not claim the false unconditional converse “source none
means hard abort.” A separate decreasing-budget theorem could show that
48 available blocks suffice for a terminal controller; no such capacity
premise or conclusion is supplied here.

## Proof route and timing

Each controller state receives a concrete source continuation:

- first phase: `3-inner` remaining circle attempts on `pending ++ unread`;
- second phase: `3-inner` remaining circle attempts, with `2-outer` later
  distinct retries after the currently running circle call;
- accepted/aborted states: the corresponding fixed result.

Source-recursion identities consume each actual ordinary result and its
returned suffix. They model map rejection, a successful duplicate, and
inner/outer retry exhaustion separately. Only a successful duplicate can
start another outer attempt; inner ordinary failure aborts.

The reachable-state invariant says that a running state's pending prefix
has detailed status `needMore`. The checked preceding leaves then establish
that a successful next block leaves no unread whole block, a hard failure
cannot be repaired by an unread suffix, and a four-block `needMore`/layout
branch is impossible. These facts prove one-block continuation equality,
followed by list induction over the actual `afterAnswer` controller.

The mathematical fold may visit the rest of the supplied list after a
halted state, but those updates ignore their answer and are explicitly
ghost padding. This is not a claim that the source consumes those blocks.
No disjoint padded four-block windows replace variable-length source calls.

## Scope boundaries

This is deterministic refinement of the pinned mathematical prefix decoder
and controller. It does not translate Rust machine execution or prove
coordinate destination uniqueness, finite-tape measure preservation,
freshness, a random-oracle coupling, or Fiat–Shamir security. The proof does
not assume one of those interfaces merely because both sides have matching
source-level recursion.

Working parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.
Borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Direct imported status source SHA:
`4864d2cda4e7ec3196d2c4ca4b084e17a59e66c9ab4800e4747bc8612d2f3c21`;
green olean SHA:
`637eeb7721c1b77841feb5de21f597418476b14cf3a3c990e249e000d7a297c7`.
All imports were already pinned in the existing NUC overlay; no cold build
or import/cache staging was needed.

## Focused build evidence

Both attempts used separate explicit root grants and the inherited
`run_higher_y_nuc.sh`, through Tailscale numeric IP `100.108.41.90`. Initial
preflight reported only `init.scope` and 42 GiB available. The retained logs
give the exact Lean 4.32.0 command with `-j1 -M9500`, target
`NestedCircleRunRefinement`, and actual cgroup limits: MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPU quota 200%.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 6.89 | 6658416 | 0 | Source recursion/exact-suffix steps checked; four needMore proof branches needed append-length guard normalization. Twelve audits standard-only, six downstream audits inherited those failures. |
| v2 | 0 | 3.73 | 6691184 | 0 | Only those four length guards changed; all eighteen audits standard-only. |

Both attempts' `.log`, `-source.txt`, and `-manifest.json` files are retained
under `experiments/nested-circle-run-refinement-nuc-vN`. Failed v1 temporary
`sorryAx` entries are diagnostic, not release evidence; none remain in v2.
The successful source equals its snapshot byte-for-byte. The final
postflight verifies 883 entries and records unchanged provenance. The
compiler slot was released after the terminal postflight, before artifact
copy/report finalization; no additional target was run.

Inherited runner scope parent:
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the working source
parent above. Native package artifacts remain a pinned-revision cache
boundary, not a package compilation replay.

Final SHA-256:

- Source/snapshot: `eb96292716d7113f21a8ccaa22f1605f12a9d4a8595670a5db963d52ab8348bd`.
- Olean: `6207695054996c0d73f35873fc4453d68eba082ef7bce7e332dbb1175ea4e170`.
- Log: `876548d998acf551e586e92a29a6c6342c82516d4d6d77fe4cf133175ba0a4da`.
- Manifest: `bc22d17b3850134b4cfd297bf29fdb055fe0aa8a2199bb19ebae5b274c240fd9`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
