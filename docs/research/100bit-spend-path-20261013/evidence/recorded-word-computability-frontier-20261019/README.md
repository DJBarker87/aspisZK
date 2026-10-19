# Recorded-log word constructor: executable caller gap

The focused ordinary-definition probe attempts to call the existing RawCutWordsFromView.buildWords from an executable wrapper. Lean 4.32 rejects it with lean.dependsOnNoncomputable. The attempt exited 1 in 18.13 seconds, peak RSS 3,023,650,816 bytes, zero process swaps; no compiled target object exists. The standard axiom print after the compiler error is not a successful executable result. Raw command, source revision, direct import/source/object pins, frozen source and compiler output are retained.

This evidence narrows an open boundary: the already checked executable fixed-word extractor is not yet a complete executable recorded-log extractor. The semantic recorded-log word constructor cannot simply be passed through as executable code.

The corrective path is in progress: compute only raw hash-state transitions through row 30, with the row-26 reseed, to select commitment frames 0, 2 and 30; separately use finite recorded-log Merkle recovery and strict typed leaf decoding to reconstruct the three words. This avoids evaluating the specification-level protocol/choice extractor or challenge maps. Both replacements must be proved equal to the retained model before caller composition. No production code changed and no 100-bit security completion is claimed.
