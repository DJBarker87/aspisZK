# Historical tool identity

The existing Full adapter comes from ProverRwCaller caller-005. See tracked
`tools/prover-rw-20261023/stage3/adapt-caller.py` and continuation
`translation-caller-005-audit.json`. Historical Aeneas flags from the retained
caller-005 preflight:

    -sequential -no-progress-bar -abort-on-error -log-debug Translate
    -backend lean -namespace ProverRwCaller -dest generated-caller-005
    -split-files -emit-json ProverRwCaller.llbc

Historical binary 4632746d… (49,419,624 bytes), b59d5188 extended; recorded path
`/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static`
is absent. Charon's old path is absent too, but the retained pv-cb pinned binary
is BYTE-IDENTICAL to its daad69be… historical pin, so it is used read-only.
Charon driver efdbe5b8… and nightly-2026-06-01 are recorded per command receipt.

The readily available Aeneas 562e1f51… is NOT silently substituted. A mechanical
comparison of the retained rng-extractor/base OCaml source against the
historical source manifest finds nine differences among 101 checked files.
This is a source-version difference, not merely a binary build-instance delta.
The original manifest and detailed comparison are retained. No extractor is
built, edited, patched, or upgraded in this job. No claim of Aeneas execution
is made without the exact historical binary.
