# R686 actual query-root invariant inventory

Read-only source/evidence map. No query sample, benchmark, or elimination was run.

## Exact selected path and source values

The frozen selected `relation_callback.rs` is SHA-256
`4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`.
Its `query_schedule` at lines 146–151 invokes
`challenge_queries_without_replacement(22, 1<<18, 64)`; on success it returns
22 unique query indices in `[0,2^18)`, and on exhaustion maps sampler failure
to `Error::Sampler`. Frozen `transcript.rs` is SHA-256
`451357c6d61e3eaf750ead4bc4f3aa5d32db9771346d798818dd331d755bb546`;
`Transcript::challenge_queries_without_replacement` lines 493–545 masks the
18-bit candidate words, ignores already-accepted duplicates, stops after 22
accepted or 64 draws, and returns an error on an incomplete list.

Frozen `r17_host_relation.rs` SHA-256
`3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801` calls
`circle_norm::Selected::new(queries)` in `opened` and computes the selected
relation root at the `lines.push` expression:
`base.x.mul(base.x).double().sub(M31::ONE)`, i.e. `2*x^2-1` in M31.

The exact selected point source is `crates/aspis-core/src/circle_fri.rs`, SHA-256
`77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b` (also
saved under R42 unchanged-source snapshots). In
`selected_circle_fiber_points_shared(20, fibers)` (lines 241–313), the accepted
domain is `fiber < 2^18`, `natural = reverse18(fiber)`, and the point is
assembled from the three 6-bit windows indexed by the low, middle and high
parts of `natural`. Those generated windows are sourced by `build.rs` SHA-256
`7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d`; the
fixed group source is `params.rs` SHA-256
`5f1e013c441f80b04c7960af8d4d3ae8ebbd295fe0031e9b60dd9e85b2be10b3`, with
`CIRCLE_GEN=(2,1268011823)` and `CIRCLE_LOG_ORDER=31`. Source helper
`point_from_group_index` uses `CIRCLE_GEN.pow(index & ((1<<31)-1))`; the
half-odds initial/step exponents are `2^10` and `2^12` for this domain. Thus,
with `n=reverse18(q)`, the selected source point has group exponent
`e(q)=2^10+2^12*n`, and its R686 root is the x-coordinate of the squared
point, with group exponent `2*e(q)=2^11+2^13*n` and x-coordinate
`2*x(q)^2-1`.

## Existing evidence and proof boundary

`R42_ADMISSIBLE_GRID_AND_QUERY_SOURCE.md` records an optimized executable check
of all `2^18=262144` valid source indices against an independent sequential
group walk. It checked all point coordinates, the circle equation, and all
`2*x^2-1` roots: `unique=262144`, no root 1, ordered-root SHA-256
`e417c33d590558595f5a27abc44cfe9fc6985b02bce7d17fcc974025033ba4a1`.
The exact check receipt/log are under
`evidence/r42-admissible-grid/roots/`; receipt marks `sampler_law=false` and
`full_privacy=false`. This is exhaustive runtime source evidence, not a Lean
root-map theorem.

Available formal results cover adjacent facts only:

* `Q22SamplerInvariants.challenge_result_valid` proves successful source query
  results are length 22, Nodup, and bounded by 262144; it does not map queries
  to circle roots.
* `R412LegalQueryEnumeration.enumQuery_injective` and
  `listQuery_injective` encode list-level legal distinct queries. That file is
  explicitly labeled a draft/uncompiled artifact; neither theorem addresses
  source circle roots.
* `R243LineNormBridge.line_coordinate_exact` proves the arithmetic fragment
  `2*x^2-1` for a supplied encoded M31 x-coordinate. It does not bind the
  selected 20-domain table point to a finite exponent or show injectivity.
* `R172CircleSamplerExecution` concerns the bounded secure-circle transcript
  sampler, not `selected_circle_fiber_points_shared`.

No inspected Lean theorem proves `q ↦ 2*x(q)^2-1` injective on all 262144
source indices or excludes 1. For successful query-sampler outputs, the source
input indices themselves are distinct deterministically; if the exhaustive
source map is accepted as the implementation claim, no query tuple can create
a duplicate root or root 1. In the proof chain those are deterministic domain
facts, not bad events to exclude with a probability loss. The possibility that
the bounded query sampler returns `Error::Sampler` remains an execution/error
case and must be handled in the actual published-view probability analysis.

The missing formal bridge is the exact table/exponent identity for the
`domain_log_size=20` fast path plus the group-x injectivity argument on the
exponent interval/coset; then compose it with `challenge_result_valid` and the
selected query-schedule correspondence. The source arithmetic suggests the
injectivity route: `e(q)` ranges below `2^30`; equality of x-coordinates of
squared norm-one group points means doubled exponents agree up to sign modulo
`2^31`. The positive-difference case forces the same `n`; the negative case
would require `e(q1)+e(q2)=2^30`, impossible since that sum is congruent to
`2^11 mod 2^12`. Root 1 would require the doubled exponent to be 0 modulo
`2^31`, impossible in this interval. This is a proof route sketch only, not
an already checked theorem.
