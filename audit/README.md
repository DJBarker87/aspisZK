# Audit probes and reference anchors

Focused cross-checks that sit outside the main build.

- `poseidon-pair-probe/`: SBF compute probe for the pool pair-parent
  Poseidon2 path. Its `program` crate is a member of the root Cargo
  workspace.
- `stwo-circle-candidate/` and `stwo-line-fri/`: generators that reproduce
  Aspis test vectors from the official Stwo sources.
