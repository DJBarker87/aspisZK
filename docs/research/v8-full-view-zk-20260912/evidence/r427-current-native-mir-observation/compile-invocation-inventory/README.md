# Charon direct-driver compile-invocation inventory

This is a read-only inventory of pinned source, the saved original release cache, and the stopped build-v2 evidence. It does not design or launch a direct-rustc replacement.

The binary target is charon-driver at charon/src/bin/charon-driver/main.rs, in edition 2024, with #![feature(rustc_private)] and Cargo features default,rustc. Its main.rs explicitly imports 24 rustc-private crates plus charon_lib, so the pinned nightly sysroot is a compile requirement. The saved Cargo fingerprint records 46 direct Cargo dependencies. Each dependency fingerprint matched one unique cached release fingerprint and artifact set; see cached-dependency-artifacts.json. Fingerprint marker bytes were interpreted as little-endian u64 to match Cargo's recorded dependency hashes. Artifact hashes come from the complete saved release-target manifest, not new remote hashing.

proc_macro2 is not a root direct dependency. The saved fingerprints of direct proc-macro dependencies macros and hax_adt_into both resolve to cached unit proc-macro2-b731dd505951052a, with default,proc-macro features and the recorded profile hash. Its cached rlib and rmeta are listed in nested-proc-macro2.raw.json.

The read-only scan of saved Cargo build-script outputs found a single native link directive: static=psm_s, with a native search path under target/release/build/psm-0054b740d3e1ad34/out. The archive and hash are recorded in the JSON. Other matching build-script output lines are rustc-cfg directives. This does not enumerate Rust compiler sysroot linking requirements.

The copied driver, wrapper, and library entry sources contain one compile-time environment macro: env!(CARGO_PKG_VERSION) at charon/src/lib.rs:59, value 0.1.223, in the separately compiled charon_lib. No such macro occurs in the driver main.rs. No package-level build.rs or relevant Cargo config was found; the two build.rs files found are test fixtures.

The fingerprint records feature set, empty rustflags, release profile hash, Cargo config hash, and dependency fingerprints, but does not preserve the full rustc argument vector. The saved build-v2 log is non-verbose and contains only Compiling proc-macro2 v1.0.96 before the stop (exit -15); it does not expose the rustc command or why Cargo reconsidered that cached unit after relocation. Exact historical rustc optimization/codegen/link flags and unrecorded inherited environment remain unknown.

compile-invocation-inventory.json is the machine-readable summary. source/ holds source/fingerprint/dep-info copies and map_cached_deps.py, map_nested_proc_macro2.py, and read_build_outputs.py are read-only inventory scripts.
