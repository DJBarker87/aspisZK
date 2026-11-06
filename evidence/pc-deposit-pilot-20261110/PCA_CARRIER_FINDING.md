# PCA draft carrier finding

This is a defect/unfinished obligation in the PCA draft, not in the frozen program. E1 is NOT MET.

PCA_State uses UInt64 for ProgramError, with builtin errors represented by ABI status codes. The pinned solana-program-error 2.2.2 has payload-bearing variants, including a String-bearing variant. A scalar ABI code is not automatically the complete Rust ProgramError value. Source archive checksum and unpacked source equality against the frozen Cargo.lock are recorded in PCA_PROGRAM_ERROR_CARRIER_REVIEW.json.

No theorem here proves that every reached deployed error lies in an injectively encoded subset, or reconstructs the exact payload from the code. The generic runtime's complete Err is therefore not justified by the present carrier. The exact helper count reference only uses two fixed builtin errors, but even its native/Lean enum association is not claimed CLOSED.

Correction to any earlier phrase “complete Result” in draft source comments: the current definitions retain their OWN complete scalar-error model Result, not a certified complete frozen Rust Result. They are not an adopted transcription. No native-to-model root, reviewed-transcription adoption or Pool promotion follows from their compilation or axiom audit.

Required repair: a full pinned ProgramError algebra (including payloads) and exact propagation in state/events/child packets, OR a proved, caller-established restriction and injective reconstruction for every reached error. Preserve abort prefixes and all effects. This needs new Lean work; it must not be assumed as a caller premise or silently hidden in a generic packet. The checked intermediate source snapshots are retained unchanged for reproducibility.
