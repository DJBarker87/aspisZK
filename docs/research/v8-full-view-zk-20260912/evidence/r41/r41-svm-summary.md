# R41 SBF/SVM evidence summary

Source stage: `/home/dombarker/project-offloads/aspis-r17-sbf-probe-20260921-r41h`

Artifacts and logs were copied without rerunning:

- `carry-build-r41.log`
- `carry-svm-r41.log`
- `carry-svm-r41.jsonl`
- `carry-svm-path-error-r41.log` (initial launch path typo, exit 127)
- `r17-sbf-probe.json`
- `r17-compact-control.json`
- `aspis_v8_performance_sbf-r41.so`
- `r41-carry-workspace-control.log`
- `r41-carry-shortcuts-control.log`
- `r41-v2-proof-mutation.log`

Artifact hashes are in `r41-artifact-sha256.txt`.

The corrected SVM launch used the same ELF and produced six JSONL observations;
all six had `accepted:false` (`total_failure=6/6`). Four low-limit runs failed
at the 1.2M/1.4M CU meter. The honest 100M diagnostic run reached the primary
terminal checkpoint, then failed with `memory allocation failed, out of memory`.
The mutated `bad-g-final` 100M run did not emit a primary-terminal-accepted
marker before the same out-of-memory failure, so it is not a checked rejection:

| case | CU consumed | checkpoint / intervals (remaining CU) |
|---|---:|---|
| honest | 23,176,531 | primary checkpoint consumed 19,981,659 CU; G chord consumed 2,051,371 CU; ordinary consumed 1,277,725 CU; original 79,168,307→76,983,000 remaining |
| bad-g-final | 20,566,079 | no primary acceptance marker; G-tree/FFT/chord and original reached the OOM path; not a checked rejection |

The SVM result is diagnostic/runtime evidence only; it does not establish
protocol or privacy closure.
