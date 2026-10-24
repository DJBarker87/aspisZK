# Material acknowledgment and derivation control

Continuation of reviewed dbc123fdc8 and proof 5296e55148. Assigned branch
codex/cx-prover-rw-20261023 only. No shipped source or backend changes.

## Scope and source order

The actual pair-forest producer checks both context fingerprints, obtains
relation-free cells, obtains active rows, and calls build_mask_material_for_layout.
That helper reserves the provided acknowledgment store before rejecting zero
entropy, encoding context, hashing the seed, constructing SeedExpander, finding
an inactive row, and sampling c1, mask-only columns, g and h1 padding in order.
The returned material is constructed from those four replies and context nonce.

The fresh PreReservedNonce acknowledgment is single-use. Layout/cell/active-row
failure occurs before its consumption; zero entropy and later sampling failures
occur after it. The outer durable reservation has already happened before any
of those material-stage failures and is not rolled back by them.

## Validation and boundaries

Work in progress. Evidence lives under rng-material/; old ledgers remain intact.
36 actual Lean launches available at entry (184/220 already used); Kani 44/60.
No full manifest or runtime/ELF/timing gate is authorized or claimed.

Exact cells/active-row source components, first_inactive_row, and the four
sampling components are initially separate unproved source cuts. They are not
primitive instructions. Hash/encoding replies and external type/function holes
remain explicit; no whole-material desired equality premise is permitted.
Physical Drop/clear, getrandom sort/result/destruction transport, old cap8 native
body/audit installation, successful byte/context-to-Raw, and L1/L2 remain open.
E1 is unchanged: ProverCommitPublicNonce40.E1. No probability law is added.
