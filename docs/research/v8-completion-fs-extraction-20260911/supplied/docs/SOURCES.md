# Sources and evidence boundaries

## Repository snapshot actually read

Repository: DJBarker87/aspisZK.
Branch: research/v8-no-work-100-20260907.
Commit: 30a303a344dbb42e24ad8f42a8804819747942bc.
The branch listing contained no visible completed one-wire repair branch when
read. User-reported local completion is not disputed; it must be reconciled.

Relevant inspected sources, all at that pin:

- experiments/PackedQueryRecord.lean (Git blob22dda3c8acfa8da93dd8bd72e0dad1bb5b0d6401)
- experiments/SelectedWireBytes.lean (Git blob08f9e8313c94569a45bfe3c932e6450fe172e718)
- experiments/SuccessfulCompleteSelectedWire.lean
- experiments/SuccessfulSelectedVerifierRun.lean
- experiments/SelectedAuthenticatedSuccessfulRun.lean
- experiments/SelectedMultiproofPrefixProjection.lean
- experiments/SelectedResidualRecoveryBound.lean
- experiments/SelectedResidualHighRecovery.lean
- experiments/SelectedResidualPrefixClassification.lean
- experiments/SelectedMiddleImageRecovery.lean
- crates/aspis-core/src/v7_merkle208.rs
- selected-wire-opening-execution-review.md
- selected-semantic-output-transition-review.md
- README.md (chronological; older sections are not necessarily current).

The experiments prefix is:
docs/research/v8-no-work-100-20260907/experiments/

Canonical pinned view:
https://github.com/DJBarker87/aspisZK/tree/30a303a344dbb42e24ad8f42a8804819747942bc

The Python wire layout was cross-checked against the pinned fixed/packed
parsers. The proposed code does not claim an independent execution of those
Lean definitions or of the Rust/SBF implementation.

## Primary external references checked

- Lean upstream opaque-value kernel fix, PR14498:
  https://github.com/leanprover/lean4/pull/14498
- Primary advisory:
  https://www.vulncheck.com/advisories/lean-4-before-kernel-accepts-opaque-declaration-with-an-unbound-free-variable
- Lean proof validation reference (also linked by upstream PR):
  https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- Aeneas project and user documentation:
  https://aeneasverif.github.io/projects/
  https://aeneasverif.github.io/aeneas/
- Bernhard, Fischlin, Warinschi, Adaptive Proofs of Knowledge in the Random
  Oracle Model, ePrint2015/648:
  https://eprint.iacr.org/2015/648

No generic Fiat–Shamir theorem from these references has been automatically
applied to Aspis. Its concrete hypotheses and security notion require review.
The supplied probability lemmas are direct first-attempt formal derivations,
not claims that a cited paper already establishes the requested final result.
