# Deployed R1 prover side-channel audit — 2026-10-22

Status: inventory in progress; D159 target not yet established. Source baseline
`89013d67f06f2b8bf1ab53339d107e60a7cca556`, branch
`codex/cx-sidechannel-20261022`. No shipped code changes are authorized here.

## Contract and scope

D159 supersedes the D143 exclusion: L1 outcomes/counts/I/O metadata, L2 source
trace, and L3 compiler/hardware behavior are separate obligations. D146 limits
statements to expressible canonical source images; it does not make arbitrary
witnesses canonical. D147–158 environment/collection semantics do not imply
constant-time behavior. E1 uniform successful OS draws and E2 atomic persistent
reservation are retained assumptions, not timing guarantees.

The route is the 64-byte `generate_for_mask_nonce` adapter with a public,
adversary-chosen proof-account nonce, then `prove_masked_retrying_with`, the
masked semantic prover, compact publication, and the z4 P_R1 checker. The
96-byte `generate()` convenience route is not substituted. Private coins and
witnesses must be distinguished: a branch on an independent private coin can
be L1-simulatable but still expose a seed-dependent L2 trace.

## Inventory

Pending source inventory and classifications.

## Findings and attempt law

Pending.

## Evidence, deployment, and next deliverables

Pending. No Lean or Kani proof has been run for this audit.
