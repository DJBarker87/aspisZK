# Computable commitment-frame replay matches the protocol

The raw replay computes only byte frames and hash states; it never executes the field challenge decoder or specification-level extractor. Pointwise successor compatibility covers public initialization, row zero, ordinary payload rows and the row-26 opening reseed. The dependent state induction proves stateBefore equals the selected literal protocol prefix state at every position through 31 under valid constructor scheduling.

The three frame theorems reuse the existing public RawCutCommitmentFrames first-read results. frameFromView_commitments_eq derives equality of the recorded-view frame bytes at exactly rows 0, 2 and 30 from valid rows through 30. No frame equality or recovered-word equality is assumed. This discharges the FrameCompatible contract needed by the saved executable recorded-run caller.

The pointwise module and dependent bridge passed focused Lean 4.32 checks: 6.76 seconds / peak RSS 3,118,104,576 bytes, and 19.8 seconds / peak RSS 2,698,346,496 bytes. Both exited 0, report zero process swaps and only standard axioms. Sources, compiler commands, revisions, import/object pins, complete axiom output and compiled objects are retained. No cold build or full regression was run.

These are working component checks under the research-branch D63 policy, not release evidence from the unified ordered build. The validity schedule remains a premise; actual source acceptance must still supply it and all semantic/opening checks. Executable word/caller composition, source refinement, event coverage, complete knowledge efficiency, privacy integration and the final two-transaction artifact remain separate work.
