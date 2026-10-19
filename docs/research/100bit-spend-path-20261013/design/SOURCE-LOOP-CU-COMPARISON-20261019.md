# CU comparison for the isolated source-loop candidate

The measured production version on `research` is unchanged: stage 1 peaks at
1,199,687 CU and actual Pool settlement at 1,188,496 CU over the six saved
fixtures. The baseline source and artifact pins are in
[the CU savings report](../evidence/cu-savings-20261019/FINAL-REPORT.md).

The separate `codex/r1-source-proof-loops-20261019` candidate at
`5c63b0bba7ceae70bad1f980a766fa65728624fc` replaces semantic iterator folds
with indexed loops, batched mutable iteration/map with explicit operations,
and the decoder with the retained proved V10 indexed implementation. These
source changes allow complete extraction without the old Iterator backend
failure or external array-operation templates. They produce different
machine code, so their CU must be measured independently.

| Fixture | Production stage 1 | Candidate stage 1 | Actual settlement, both |
|---|---:|---:|---:|
| transfer-13 | 1,199,648 | 1,273,470 | 1,137,397 |
| transfer-255 | 1,199,567 | 1,273,389 | 1,174,671 |
| transfer-1023 | 1,199,687 | 1,273,509 | 1,171,579 |
| withdrawal-13 | 1,198,225 | 1,272,047 | 1,150,958 |
| withdrawal-255 | 1,198,264 | 1,272,086 | 1,188,496 |
| withdrawal-1023 | 1,198,386 | 1,272,208 | 1,185,236 |

The candidate adds exactly 73,822 CU to stage 1 on each saved fixture;
settlement is unchanged. It does not meet the newer 1.2M target. The
contribution of each individual source change has not been isolated. This
is not evidence of differing CU from repeated execution of identical code,
or a change in the cryptographic challenge parameters.

The observed candidate checks passed: 14 core tests, 23 checkpoint tests,
1,233 byte-identical codec outputs, the baseline's exact ordered 583 hash
calls (349/234), linked-ELF stack validation, and six runtime fixtures.
Only the auxiliary repeated-input histogram was sorted; ordered hash calls
were compared in their original order. The candidate ELF hash is
`2e3517d872676c9515b8c5bfe20e588f1c5e33ddaad6a6742e7bdf30ebe86ff8`.
These observations concern the specified fixtures and gates, not a universal
cost bound or full source-equivalence theorem.

The primary commands, receipts and runtime JSON remain on the NUC under
`/home/dombarker/project-offloads/aspis-r1-source-proof-loops-root-20261019/`
in `runs/`, `runtime/` and the comparison JSON files. This note records the
observed results; the curated evidence packet has not yet been copied into
the repository. The new candidate's injection gates and full-random-mask
measurement remain pending. No candidate source has been merged into
`research`.

The inline-only follow-up `de42cba00380dcae8bc3b86590fade37dfb3a88c` adds
`#[inline(always)]` to `decode_k_value`, without changing its function body.
Its SBF build passed (5.504s, maximum process RSS 232,956 KiB, swaps zero,
6 GiB high / 8 GiB maximum / swap disabled). Its artifact and CU comparison
are still pending. NUC SSH at `100.108.41.90` became unreachable during the
follow-up; focused proof work continues locally under the shared memory
guard. The pending experiment must not be described as a recovered CU
result.

The generated semantic field operations and increasing boundary loop are
proved in `2892f6cfd`; actual batched-value canonical residues and exact QM31
interpretation are proved in `60a8a8129`. These are focused working checks
of the isolated candidate. Full source/caller composition and the clean
ordered release build remain open.
