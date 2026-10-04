# R565 initial-claim-plus-one — proposed diff and run plan

Status: **plan only**. No R565 source copy, build, runtime, or benchmark has
been launched. The root must review this diff and complete R563's source
dependency check before any application or execution.

## Base and allowed change

The base is the isolated R555 `recipient_zero`, seed-1 host diagnostic:

- R555 candidate `performance.rs` SHA-256:
  `1b6dc78ceb691ffa6c6176045442d4779ca309f4a1cd226a8d3a131ec0cf553a`.
- R555 adapter `payment_extraction.rs` SHA-256:
  `703148073c8f70257fc7ff87c823e0a28bff9d96febdf32274e8779998401090`.
- Frozen selected source revision:
  `6677d5f1310ff7373301fbd79f186278f772e68a`.
- Existing R555 fixed artifacts:
  `.r21-scratch/r555-zero-output-rejoin/zero-output-rejoin-evidence/run-zero-output-seed1/`.

The proposed execution enables a new host-only cfg
`v8_initial_claim_plus_one`. The sole semantic-wire modification is exactly
`initial = initial.add(K::ONE)`, after both C1/C2 messages and roots are built
and compared to the immutable R555 artifact, and immediately before `v[0]`
and `semantic_start` consume the claim. It does not alter committed trace,
public statement, transition, binding, messages, roots, salts, verifier,
positivity relation, canonical/authentication controls, seed, or oracle hook.

## Exact seams

`performance.rs` base lines 222–244 build selected messages/C1 root `a`, C2
messages, initial field claim, C2 root `b`, then set `v[0]`; lines 258–259 call
`semantic_negative_fixture(... semantic_start(..., initial, ...))`. The
proposed block is inserted only between the C2-root construction and that
claim use. It byte-compares `public.bin`, `binding.bin`, and `transition.bin`
to R555, parses R555 `proof-1.bin`, and requires its C1/C2 roots equal newly
constructed `a[18][0]`/`b[18][0]`. The eventual wrapper must additionally
record external SHA-256 values for the three input files, R555 proof, and new
inputs; it must fail on any mismatch.

`payment_extraction.rs` base lines 135–151 construct the genuine first-round
polynomial using `terminal_with_g` and `interpolate_degree27`, assert
`first_boundary_wrong`, program exactly one post-round-zero squeeze, and
require `z0=0`. The proposed first-round check builds independent coefficient
arrays at `eta=0`, `eta=1`, and the actual `eta`; it asserts all 28 coordinate
equalities `P(eta)=P(0)+eta*(P(1)-P(0))`. It temporarily assigns only
`s.eta`, restores it before the existing boundary/oracle code, and never calls
an oracle/transcript method. This is field and terminal evaluation plus
interpolation, not an RO call or a runtime-cost/reduction claim.

## Required retained checks

The eventual candidate must retain R555's genuine-polynomial assertion
`first_boundary_wrong`, single programmed first `z0=0` squeeze, full body
construction before the selected verifier calls, raw and typed public decode,
transition decode, private-install `Domain`, checked-extractor rejection,
canonicality/active-row assertions, C1/C2 authentication, corruption,
truncation, and noncanonical controls. It must run only the one existing seed
and make no nonce, second-seed, or challenge search.

No conclusion about SHA-256, an oracle probability, admissible witnesses,
privacy, soundness, or end-to-end security follows from this proposed case.
