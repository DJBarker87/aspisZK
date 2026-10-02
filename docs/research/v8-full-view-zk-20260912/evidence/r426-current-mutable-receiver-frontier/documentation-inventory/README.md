# R426 documentation inventory (scratch draft)

This folder indexes only the saved R426 mutable-receiver diagnostic and its directly cited R396, R419, and R425 provenance. It contains no copied build trees or unrelated scratch material. It is not a formal release bundle and does not settle the serialized comparison or source semantics.

The actual R426 capture completed the Charon `--print-original-ullbc` command once: Charon exit 0; GNU time wall 14.45 s, peak RSS 625,372 KiB, swap 0; systemd limits MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128. The saved output has serialized LLBC SHA-256 `ed43306eac05443a2f4f91121ba8e943a000a66b0d7273eabc40735c64c6f15d` and original-ULLBC stdout SHA-256 `203ba64981a75e9348e96bdf2920f1905f42c6d756de3c644e60006a440ab412`. This is Charon output after MIR translation and before its LLBC cleanup passes, not a raw rustc MIR dump. No Lean target exists, so axioms are N/A.

The initial exact comparison gate remains recorded as failed: it compared the serialized capture to R396 and returned false after normalizing the two declared operational option fields. The Charon child exited 0; the launch wrapper exited 1 on that assertion. The result, stdout/stderr, GNU time, source-hash checks, and preflight files are indexed here. The original README, manifest, and launch plan say the run was not launched because they are pre-launch snapshots; they remain unchanged and are explicitly marked as history.

The first missing provenance is the exact rustc MIR origin of the selected `try_fold` receiver: LLBC records `Copy(Local 1)` with mutable-reference type and the printed ULLBC records `copy self`, but no saved raw MIR statement/query trace ties that occurrence to a temporary reborrow, CopyForDeref, or Retag event. Pinned compiler/Charon excerpts document generic paths only.

`inventory.json` enumerates authoritative paths and SHA-256 values, exact output metrics, pinned source hashes, and the finite tooling boundary. This is a scratch draft for lead review; it does not make a final equality or semantic claim.
