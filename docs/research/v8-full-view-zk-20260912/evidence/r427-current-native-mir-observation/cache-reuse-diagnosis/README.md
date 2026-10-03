# R427 Cargo cache reuse diagnosis (read-only)

This diagnosis explains only the first R427 Cargo build guard stop. The guard saw `Compiling proc-macro2 v1.0.96` and terminated Cargo with status -15 before any Cargo package compiled successfully. The cgroup peak was 538,214,400 bytes, swap stayed 0, and the existing candidate driver stayed at its pinned pre-build SHA. GNU time inside the worker was terminated with Cargo and wrote no child accounting; do not interpret its absent metrics as zero. The outer GNU-time and cgroup records are retained under `clone-build-preflight/build-attempt-v2/`.

The clone-time target cache manifest verified parent and copied caches byte-for-byte and mode-for-mode. A post-stop read-only inventory found 21 shared `proc-macro2` cache metadata/artifact paths still byte-identical. The cached library fingerprint JSON (`release/.fingerprint/proc-macro2-b731dd505951052a/lib-proc_macro2.json`, SHA `f6e1e4639d7c19824845c43ac3073f2f2a65f44f848549c88bf3ed33608300e1`) records features `["default", "proc-macro"]`, profile ID `2305346612590964689`, empty `rustflags`, config ID `9396254390672932401`, and rustc ID `16711085482362714645`. Its rlib/rmeta hashes match in parent and candidate. The parent `charon-driver` fingerprint also has an exact candidate match and records release profile ID `12468216108105302490`, `default,rustc` features, and empty `rustflags`. The existing nested-dependency inventory shows both `macros` and `hax_adt_into` use this same cached proc-macro2 unit.

The v2 Cargo attempt added only `release/.fingerprint/proc-macro2-f18635ddfd7f68bb/invoked.timestamp` to the candidate before termination. It produced no fingerprint JSON or object for that variant. Thus the saved data show that Cargo selected another unit but do not reveal its expected feature/profile/rustflag values or the reason. The root Cargo manifest and lockfile retain the pinned hashes; no inspected workspace/user `.cargo/config` file or custom profile stanza exists. The build worker set `CARGO_HOME`, `CARGO_TARGET_DIR`, `CARGO_NET_OFFLINE`, and PATH, while inheriting other variables. The previous invocation did not snapshot that inherited environment. Fingerprint metadata is evidence of empty rustflags for the cached artifacts; it does not prove the full prior process environment.

One read-only `cargo tree --edges features --invert proc-macro2 --locked --offline` inspection was attempted for parent and candidate. It exited 101 because the offline Cargo home lacked `crossbeam-deque v0.8.6`; no build was run. The raw output/status are retained here. No Cargo retry or cache edit was performed. This unsuccessful tree query is not evidence for the build miss cause.

## Files

- `fingerprint-metadata.stdout.json`: remote parent/candidate artifact, fingerprint, depfile, and Cargo registry metadata snapshot.
- `fingerprint-comparison.json`: strict comparison of all 21 common proc-macro2 artifacts and the single candidate-only interrupted marker.
- `config-env.stdout.json`: inspected Cargo configuration file presence/hashes and relevant safe environment keys; no configuration files were found and no relevant environment variables existed in that separate SSH process.
- `cargo-tree-features.*`: the failed, read-only feature-tree query.
- `collect_fingerprint_metadata.py` and `compare_cached_fingerprints.py`: reproducible collectors/comparator; they do not invoke Cargo.

This audit does not identify why Cargo requested the new fingerprint variant. The lead selected a separate direct-rustc diagnostic route; it is prepared and reviewed separately, without claiming that route reconstructs the previous Cargo invocation.
