# Recorded public statement and ordinary extractor core

RawCutWordsFromRunPublicValid defines the public statement parsed from the recorded run's exact public bytes. A successful fixed-public extractFromRun returns a witness satisfying Rspend; the theorem retains the precise successful public parse as an explicit premise.

RawRecordedPublicSpendExtractorCore is an ordinary computable wrapper: parse this recorded public, then call extractFromRun, with only the run and the private finite byte tape as inputs. The definition itself is checked. The wrapper's transport/completeness theorem is separate work and is not claimed here. It does not replace the already checked fixed-public recorded-run completeness theorem.

Both focused Lean 4.32 checks exited 0, report zero process swaps and standard axioms only. Exact metrics, source revisions, commands, hashes, logs and compiled objects are included. This is working component evidence, not a clean unified-manifest release or a complete source/runtime soundness proof.
