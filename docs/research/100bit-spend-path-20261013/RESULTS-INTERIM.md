# 100-bit spend path: interim NUC receipts

This report records the artifacts collected from `dombarker@100.108.41.90` at
`/home/dombarker/project-offloads/aspis-100bit-path-20261013`. The result
directory was `results/100bit-path-20261013`. Stage labels and receipt
`source_revision` strings are preserved as recorded. These earlier receipts
were not frozen by a stage manifest; the available stage ELF hashes are listed
as artifact identifiers, not as a claim of manifest provenance.

All observed stage receipts ran in separate named systemd scopes with
`MemoryHigh=4294967296`, `MemoryMax=6442450944`, and
`MemorySwapMax=0` (4 GiB high, 6 GiB maximum, no swap). Receipt JSON records
per-stage peaks and exit status. No matching active experiment scopes were
listed at collection time, and the `kernel4b` build and test receipts already
show completion.

| Stage | Recorded source revision | CU diagnostic (tx1 / tx2) | Build / test / measurement status | ELF SHA-256 |
| --- | --- | ---: | --- | --- |
| `inline` | `7742957648c33cf045eb6a672e7c7cc796b61087+inline-stage1` | 2,275,382 / 2,230,323 | SBF build 0; diagnostic 0; no test receipt collected | `97f90f11e353728432884072767e408841698c80c96f014c9e7ace4ad602008e` |
| `sampler` | `7742957648c33cf045eb6a672e7c7cc796b61087+sampler-stage2` | 2,031,357 / 2,230,323 | SBF build 0; test 0; diagnostic 0 | `e032efd78eb31a5a91c90071ade33c0e90794946f002a931f15e1663681a1e19` |
| `weights` | `7742957648c33cf045eb6a672e7c7cc796b61087+weights-stage3` | No diagnostic receipt found | SBF build 0; test 0 | `db908327a56c05c1e094c1b6efd7f4d7943d47a3db9e6f8edd2a5c9266a81917` |
| `weights3b` | `7742957648c33cf045eb6a672e7c7cc796b61087+weights3b` | 2,031,357 / 1,888,680 | SBF build 0; test 0; diagnostic 0 | `ea9e9b555e0e76f3eaafc82df35054d8aac06b4a12ec4fd6728d808331c5010b` |
| `kernel` | `7742957648c33cf045eb6a672e7c7cc796b61087+kernel-stage4` | No diagnostic receipt found | SBF build 0; test 101 | `7622e6bb762c1eb05dccb454dd6c01818fd2f5d3c9e2e4f577736cab4bac6fdb` |
| `kernel4b` | `7742957648c33cf045eb6a672e7c7cc796b61087+kernel4b` | 1,806,103 / 1,691,283 | SBF build 0; test 0; diagnostic 0 | `b64a65875dd0bf45cf4b300d9d31a37eb9ab00e5f98e935f34ecfbaf8bea0750` |

The `kernel` test receipt records failure in
`prefix_and_public_transcript_reject_bad_framing_and_field_encodings`; the
`kernel4b` receipt records that test passing. No `kernel4b/stack/stack-audit.json`
or CU diagnostic receipt was present when the source snapshot was captured.
Both became available afterward and were copied without refreshing the frozen
source snapshot. The kernel4b stack audit matches the recorded ELF SHA-256 and
reports zero reachable stack diagnostics.

Stack-audit JSONs were available for all six stages after the later kernel4b
artifacts were collected. The `weights` audit reports six reachable
diagnostics in `Weights::pair`, including a 6,200-byte stack offset against
4,096 bytes and call-frame overwrite diagnostics. The `kernel` audit reports a
reachable `r1_semantic::verify` stack offset of 4,136 bytes against 4,096
(40-byte excess; estimated frame 4,224 bytes). The `inline`, `sampler`, and
`weights3b` audits report zero reachable stack diagnostics; their recorded
diagnostic functions are absent from the linked ELF. These are the audit
outputs as recorded. The `kernel4b` audit has zero reachable diagnostics and 34
diagnostic functions absent from the linked ELF.

Evidence copied under [`evidence/`](evidence/) includes the stage receipt JSONs,
bounded build/test/measurement logs, and the available stack-audit JSONs. ELF
binaries, fixtures, keyfiles, linked text, symbols, and multi-megabyte
disassemblies were excluded. [`source-snapshot-kernel4b.json`](evidence/source-snapshot-kernel4b.json)
is **partial-baseline-only**: its SHA-256 values cover 332 paths selected from
the local baseline Git index at `7742957648c33cf045eb6a672e7c7cc796b61087`.
That index omitted untracked probe and program files, including the probe crate
sources, so this artifact does not prove complete kernel4b source provenance.

The current detail-stage5 source tree was frozen separately in
[`source-snapshot-detail-stage5.json`](evidence/source-snapshot-detail-stage5.json)
and [`source-tree-detail-stage5.tar.gz`](evidence/source-tree-detail-stage5.tar.gz).
The snapshot captured 364 source files (9,482,703 bytes) at
`2026-10-13T15:17:15.019828+00:00`; the compressed source archive is 1,819,223
bytes. All 364 archived files were rehashed and matched the snapshot. The
archive SHA-256 is
`aa43f3f0e41ef3efa1480385983ccbb9c4b3f6f346776c3a7e33f38d19a8c3c8`; the
snapshot JSON SHA-256 is
`a43088af284f339515661deff87a3c8f8c14c3dc9e552a7f5bdcc2778c012dcf`.
The selection reads the remote filesystem directly and includes the new
`aspis-r1-cost-probe` crate, `programs/r1-cost-probe`, root Cargo files,
Rust sources/manifests/build scripts in crates, and source files in
`tools/r1-cost-probe`. Results, fixtures, key directories, caches, targets,
binaries, and `.git` were excluded. No `.git` metadata is present in the remote
experiment directory; `+detail-stage5` is a synthetic receipt label. The 332
paths shared with the earlier partial snapshot have unchanged hashes; 32 paths
are newly included there. The complete snapshot hashes match the corresponding
files in this active local worktree. This provides an exact detail-stage5
source artifact, but the earlier partial snapshot cannot establish exact
kernel4b-to-detail source ancestry for the omitted files. The lead reports
three instrumented-file differences between kernel4b and detail-stage5; this
evidence set cannot identify or reconstruct those three predecessors because
the kernel4b path manifest omitted the untracked probe crate.

The later `detail-stage5` receipts record source label
`7742957648c33cf045eb6a672e7c7cc796b61087+detail-stage5`, SBF build exit 0,
and diagnostic exit 0 in the same 4 GiB high / 6 GiB max / zero-swap caps. The
diagnostic reports 1,829,280 CU for tx1 and 1,715,919 CU for tx2 at k=10, both
completed. Its ELF SHA-256 is
`ca03054dd95c105c1494e7d908b7d1c6ed4df8ce5895a1c69f05ea4d82c92a56`; the
stack-audit receipt matches that hash and reports zero reachable stack
diagnostics (34 diagnostic functions absent from the linked ELF). No test
receipt for detail-stage5 was collected.

This is a mechanical receipt inventory only; it makes no security or viability
determination.
