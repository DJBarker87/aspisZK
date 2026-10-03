# Aggregate C1-total build environment recovery

This is a read-only recovery from the current NUC staged tree
`/home/dombarker/project-offloads/aspis-r117-joint-privacy-stress-20261003-a`.
No build, source edit, or runtime check was performed.

## Compiled flag proof

The current release fingerprint is
`bin-aspis-v8-performance-host.json`, SHA-256
`19babcc311c0839963ba1912ddba986cdb6b68230d743afa3e1acfd2ecaba7a2`,
from fingerprint directory `aspis-v8-performance-host-baa49c1c41541978`.
Its `rustflags` array contains the complete selected flag list, including
`--cfg v8_complete`, `--cfg v8_performance`, `--cfg v8_compact_workspace`,
and `-A unexpected_cfgs`. This proves the compiled fingerprint used those
flags; it is stronger than the presence of `rustflags.txt` alone.

The staged `rustflags.txt` SHA-256 is
`df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`.
Its token sequence agrees with the fingerprint `rustflags` array.

## Invocation and overflow-check evidence

The preserved build logs record this release invocation:

```
/home/dombarker/.cargo/bin/cargo build --offline --locked --release --jobs 1 \
  --manifest-path docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml \
  --bin aspis-v8-performance-host --features insecure-spend-fixture,selected-v7-kernels
```

`build-initial-preserve-ledgers.log` records exit 0, 11.05 s, and 546,284 KiB
RSS; `build-initial-preserve.log` records exit 0, 11.05 s, and 544,656 KiB RSS.
Neither log is verbose and neither contains `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS`
or an emitted rustc `-C overflow-checks=on` command. The fingerprint has a
profile hash but does not render the boolean setting. A text search of the
staged tree outside `target` found no retained overflow-check environment
record. Therefore this bundle proves the actual RUSTFLAGS, but does **not**
prove the requested overflow-check setting from preserved evidence.

A later build must record the environment and verbose rustc command if that
setting is a release condition.
