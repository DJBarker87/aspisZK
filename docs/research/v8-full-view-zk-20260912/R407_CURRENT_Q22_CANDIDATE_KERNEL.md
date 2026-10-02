# R407 q22 candidate kernel

The promoted result identifies the q22 scan’s projected result under the independent-answer interpreter with an eight-candidate uniform 18-bit block model.

The equality is proved for every starting ScanState. The recurrence uses the literal scan updates, including duplicate handling, the boolean stop flag, and the 64-draw cap, and preserves the result value including its failure count. It compares the projected result, not the returned transcript state or a full-trace distribution. It does not prove the shared memoized-oracle law, uniform accepted tuples, or a security bound. The next stated bridge is cache-hit loss and kernel relabelling/uniform-success-query law.

See [R407Q22CandidateKernel.lean](lean/AspisV8R19/R407Q22CandidateKernel.lean) and [its saved evidence](evidence/r407-q22-candidate-kernel/README.md). The original compile receipt is preserved; a separate read-only cache audit documents the R406 imported source/cache identity that was not included in the receipt’s direct-local-import map.
