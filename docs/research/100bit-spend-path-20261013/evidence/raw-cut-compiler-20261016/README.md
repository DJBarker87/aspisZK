# Recorded-query commitment-word compiler

These focused NUC checks prove the recording/annotation oracle-program transformation, reconstruct the original transcript from its finite recorded answers, and construct all three word maps from the actual commitment cuts. Acceptance, adaptive public statement, membership-failure probability, and total distinct-query count are preserved. The concrete `buildWords` takes only the recorded view; it has no oracle parameter. Existing Merkle and typed-codec proofs are reused.

The strict commitment-record codecs imply the root-parser equations for all three actual sampler first cells. The semantic/opening reader preserves successful parsing, challenges and functionals under constructed metadata; its semantic messages may change with the C2 callback. Cut/full word equality uses the shared collision exclusion.

This is not a closed 100-bit theorem, an efficient extraction theorem, or a Rust verifier refinement. Concrete oracle-decoder completion and accepted-source terminal obligations remain open.

All targets exited 0, process swap was 0, and printed axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`. Each subdirectory retains exact source hash/base revision, import-object pins, command, cap, wall time, RSS and axiom output. Checks used Lean 4.32.0, one worker, 4 GiB MemoryHigh / 6 GiB MemoryMax / no cgroup swap. No full regression was rerun.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `CanonicalCutOpening` | 1.796 | 3535776 | 3 |
| `CanonicalCutTypedProjection` | 1.525 | 3536788 | 4 |
| `CanonicalCutWordProjection` | 1.48 | 3533392 | 1 |
| `CanonicalCutEnrichedTranscript` | 2.216 | 3595560 | 6 |
| `RawCutTranscriptRun` | 1.624 | 3630568 | 5 |
| `OracleProgramRecording` | 0.924 | 1824216 | 5 |
| `OracleProgramLawExt` | 0.85 | 1804184 | 2 |
| `RawCutProverCompiler` | 1.658 | 3634128 | 5 |
| `RawCutCompilerLaw` | 1.773 | 3631376 | 3 |
| `OracleProgramReplay` | 0.886 | 1813352 | 4 |
| `RawCutWordsFromView` | 2.196 | 3640480 | 5 |
| `RawCutCommitmentFrames` | 40.085 | 5039416 | 6 |
| `CanonicalCutSemanticRead` | 4.089 | 3622040 | 6 |
