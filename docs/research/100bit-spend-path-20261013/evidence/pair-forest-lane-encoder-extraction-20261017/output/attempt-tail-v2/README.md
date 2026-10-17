# Lane encoder output-tail extraction (attempt tail-v2)

This is a focused Aeneas extraction of the successful output-buffer construction
in `programs/aspis-pool/src/pair_forest.rs::encode_lane_from_authenticated_result_v1`.
It excludes the preceding validation guards. The retained Rust source is
`input/lib.rs`, SHA-256 `5b1a73f6969d698dcd2ede7784648b76bc30675642c957ce60baaf277fc1f7e7`;
the extracted target is `encode_lane_bytes_tail_v1`. Its body starts from the
same zeroed 768-byte output and writes the same header fields, lane/master data,
tree metadata, checked index bytes, root digest and twenty frontier digests.

The production method uses a mutable tree subslice and iterator loops for the
twenty frontier entries. This focused source cut flattens tree-relative offsets
to the equivalent full-output offsets and expands the fixed twenty writes to
literal indices. It retains the production digest helper, whose eight element
copies are expanded in this cut as well. Thus the extraction establishes the
cut function's output behavior; using it for the production helper still needs
the explicit offset/loop correspondence and the omitted validation-success
premise. It does not yet prove the strict encoder/decoder roundtrip or the
`StateLink` readback relation.

Pinned inputs are the same sources listed in `../input/source-manifest.json`.
The focused tail target was built on `dombarker@100.108.41.90`, rustc
`1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`, in
`aspis-lane-encoder-tail-v2-20261017.scope` with `MemoryHigh=4G`,
`MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Expected work was a small
release Rust compile followed by Charon and Aeneas; the observed stages all
completed successfully:

| Stage | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| Rust release | 0 | 0.11s | 121,964 KiB | 0 |
| Charon | 0 | 0.25s | 183,816 KiB | 0 |
| Aeneas | 0 | 1.73s | 375,408 KiB | 0 |

The exact commands and tool binaries are recorded in `../run-tail-extraction.sh`;
stage logs and generated outputs are retained beside this file. Generated
Lean SHA-256 values are `Types.lean`:
`8edd7b562fa38577e7abaf379bf702bac3fc2dc8e90d776bd18c487c3177d8f7`, and
`Funs.lean`:
`06d4efdfe9a2b21aecdbc49bf664db41bb5338e8cf5d00028ec80c0bbe4ec847`.
