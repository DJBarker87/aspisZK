# Literal indexed-prefix facts

This bundle preserves the focused NUC evidence for `LiteralIndexedPrefix` and `LiteralReadAtFacts`. The former proves deterministic take/index/drop reconstruction and indexed reader exposure; the latter exposes successful staged-row reads. These are list and Option plumbing results only. They do not establish acceptance, transcript provenance, byte-source correspondence, or a security conclusion.

`LiteralIndexedPrefix-a` compiled in 1.49 s (peak RSS 3,584,740 KiB, swap 0); `LiteralReadAtFacts-b` compiled in 1.74 s (peak RSS 3,584,292 KiB, swap 0). Both used MemoryHigh 4 GiB, MemoryMax 6 GiB, MemorySwapMax 0, TasksMax 128. The earlier `LiteralReadAtFacts-a` failure is retained and classified failed; no attempt was rerun during packaging.

The object archive contains final target objects and direct-import objects. The four pinned runner/environment files and exact source snapshots, receipts, logs, time logs, and hash sidecars are preserved. See `source-manifest.json` and `SHA256SUMS`.
