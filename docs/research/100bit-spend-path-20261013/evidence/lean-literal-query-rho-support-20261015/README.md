# Literal query and rho support

`LiteralQueryRhoSupport.large_support` proves a deterministic conditional implication: given row 31 and 32 validity, a successful query-data read, successful q22 decode, the two explicit classifier no-hit premises, the first-query match checks, and the final residual identity, the same decoded data has matching support at least 9558. This is not an acceptance-coverage theorem or a probability result, and it does not establish these premises from a transcript accepted by the full Pool program.

The final target `R1LiteralQueryRhoSupport-b` compiled in 2.62 s with peak RSS 3,623,752 KiB, zero swap, under 4 GiB MemoryHigh, 6 GiB MemoryMax, swap disabled, TasksMax 128. Failed attempt a is preserved. Its source and failure log are included alongside the successful attempt artifacts.

The deterministic object archive contains the target and its four direct-import objects. Exact source snapshots, receipts, logs, time logs, sidecars, source pins, and runner/environment snapshots are listed in `source-manifest.json`.
