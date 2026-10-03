# Default-cfg result retained

`build7` and `run5` used no `RUSTFLAGS` and no
`CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS` environment setting. They are retained
as a default-cfg diagnostic result only. They must not be described as an
execution under the frozen selected-host flag set. A later selected-flag run,
if green, is separate evidence.
