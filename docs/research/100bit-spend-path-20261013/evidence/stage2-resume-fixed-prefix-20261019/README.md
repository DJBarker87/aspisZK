# Stage-2 resume fixed-reader-prefix proof

This focused Lean result proves the successful fixed-width reader operations in
the resume body’s source order: raw state, two roots, gamma, kappa, alpha[0],
alpha[1], then rho. For all four `WideExact` values and `rho`, it exposes the
exact raw bytes and successful decoder result. It also exposes each checked
cursor advance. The E/K read facts reuse the independently checked
`Stage2ReaderSuccess` owner from the stage-2 reader packet.

The copied Lean `readPrefix` is a source-cut adapter, not an extracted
declaration from `resume`. Its correspondence pin is c8 source
`c8ea8dd49c81ab970b9dbee8d8b47718f9beb005`, `verifier.rs` bytes
15556:17017 (`stage2_resume`, SHA-256
`e6f4fa228b159f8c74158e083cfe439b158f841d464490e076ac65579df53bc8`). The
read sequence ends at `rho = r.k()?` immediately before the query-array
`from_fn` and loop. The theorem concerns the adapter's successful result and
does not prove it is a theorem about successful whole-resume execution.

Checkpoint authentication/hash verification, heap allocation, query-array
construction/validation, later semantic-alpha/z/claim/rhs/power/weights reads,
and final cursor/end equality are outside this result. The reader packet still
uses explicit arbitrary decoder and array-unwrapper fields; this proof does
not instantiate them with concrete field decoders or establish decoder
canonicality. The whole `resume` Aeneas attempt remains failed at mutable
region closure; its failure is retained in the earlier resume-v2 candidate.

The native focused check used Lean 4.32, `MemoryHigh=512 MiB`,
`MemoryMax=2 GiB`, and swap disabled. It exited 0 in 1.305 seconds; process RSS
was 2,651,236 KiB, cgroup peak was 300,847,104 bytes, and scope swap peak was 0.
The theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
Exact command, configuration, import pins, logs, and receipt are included.
OLean binaries are intentionally omitted.

The read sequence is currently a manually isolated Lean adapter. Its equality with a generated prefix cut and its reachability from successful whole-resume execution are separate OPEN source obligations.
