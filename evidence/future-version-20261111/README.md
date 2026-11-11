# Future-version one-transaction experiment, 11 November 2026

Evidence for `docs/research/future-version/ONE-TX-EXPERIMENT.md`. Unproved
measurement evidence; nothing here is adopted.

- `host/`: the scripts run on the build host (scope wrapper with admission
  check, SBF build, driver build, run, and the three round drivers).
- `out/<ELF>/`: exact environment, command, lock-file hashes and ELF hash and
  size for each SBF build; `out/driver.sha256` for the last driver build.
- `receipts/<attempt>/`: admission log, cgroup limits, exit status,
  `/usr/bin/time -v` log, cgroup memory and swap peaks, stdout and stderr.
  `B*` are SBF builds, `D*` driver builds, `M*` measurement runs.
- `measurements/<ELF>-<fixture>.json`: one record per ELF and fixture with the
  source revision, ELF and input hashes, program CU per mode, phase intervals
  and full program logs.

No ELF, key or build cache is committed. The host workspace is
`/home/dombarker/project-offloads/future-version-20261111`.
