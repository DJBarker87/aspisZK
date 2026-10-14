# Incremental candidate reuse evidence

This bundle preserves focused NUC compile evidence for five Lean modules at source base `209663b6e8bd07a5067eb5dce3cf11e02e438a0d`: semantic padding, incremental joint candidates, the incremental candidate loop, candidate cost, and the final candidate-reuse checkpoint.

The manifest records 14 receipt-backed attempts: 8 failures, 1 superseded green, and 5 final greens. The historical green `R1IncrementalJointCandidates-incremental-joint-candidates-b` is retained; attempt g is the final source-matched green. All five final source files match their successful attempt snapshots and sidecar hashes. The final object files are stored in `objects/candidate-reuse-objects.tar.gz`, whose members and SHA-256 values are listed in `source-manifest.json`. Runner and environment files are preserved under `runner/` and hash-pinned in the manifest.

The final checkpoint, `R1CandidateReuseCheckpoint-candidate-reuse-checkpoint-a`, exited 0 in 1.38 seconds with peak RSS 3,537,744 KiB and zero swap under `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`. Its 20 `#print axioms` reports use only the manifest-listed standard axioms. All successful attempt logs were checked against the same allowed set.

This bundle records the stated Lean candidate-bound and incremental plumbing results only. It makes no claim about an executable decoder, numerical security, or Rust/source correspondence. `GammaSubfieldBound` and `FractionalLiftInvolution` are outside this bundle.
