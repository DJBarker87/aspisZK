# R427 raw MIR observation build/cache preflight (read only)

## Selected observation point and native Debug behavior

Lead-selected hook location is the nonlocal-function branch in pinned `charon/src/bin/charon-driver/translate/get_mir.rs`: after `tcx.optimized_mir(rust_def_id)` returns and before `Some(body.clone())`. The native rustc `DefId` is available there, so the exact filter can require `!rust_def_id.is_local()` and `tcx.def_path_str(rust_def_id) == "core::iter::traits::iterator::Iterator::try_fold"`; the requested `ASPIS_R427_OBSERVE_MIR=1` guard only enables the diagnostic. It runs before cloning and before Charon translates operands. The body is returned unchanged. R396 selected `monomorphize=false`; `get_mir_inner` only calls `hax::substitute` when monomorphization is enabled.

`rustc_middle::mir::Body` derives Debug and contains the basic-block table; `BasicBlockData` and `BasicBlocks` also derive Debug. The formatter is not a complete field-for-field MIR serialization: `StatementKind` and `TerminatorKind` have custom Debug implementations, and `Statement`/`Terminator` Debug only forwards to `kind`, omitting their `source_info` (and statement debuginfos). Custom `Debug for Rvalue::Use` prints the `no_retag ` prefix only when `WithRetag::No`; retag Yes is represented by no prefix. Thus the body Debug does expose the retag distinction but not the explicit `WithRetag::Yes/No` token. `WithRetag` itself derives Debug. The lead's unverified draft adds a read-only walk printing explicit Use tags, statement/terminator source info, call operands, and argument spans alongside body Debug.

The current lead draft uses the pinned API shape `StatementKind::Assign(pair)` where `pair: &Box<(Place, Rvalue)>`, then inspects `&pair.1`; this matches the boxed tuple variant. `BasicBlocks` dereferences to `IndexVec`, so `iter_enumerated()` is available; `Call.args` is `Box<[Spanned<Operand>]>`, with public `.node` and `.span`. The draft is uncompiled and remains lead-owned.

The earlier `translate_bodies.rs:155–157` hook is retained as historical alternative; it is not the selected insertion point.

## Pinned workspace and cached release state

- Repository `/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon`, HEAD `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.
- Tracked source files inspected are unchanged. The repository is not fully clean: `git status --short` also reports an unrelated untracked `?? "\/"`; do not copy it into a candidate. A source clone/archive of the exact commit avoids that unrelated path.
- Cargo package/workspace is `charon/Cargo.toml`, package `charon` v0.1.223. The relevant target is `--bin charon-driver`; wrapper target is `--bin charon`. No Cargo `build =` field or `build.rs` exists.
- `charon/rust-toolchain` pins nightly-2026-06-01 with rustc commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (rustc 1.98.0-nightly); Cargo is 1.98.0-nightly. The exact `rustc -Vv` and `cargo -V` output is in `preflight.json`.
- Existing `charon/target` is 2.2G, including release dependencies and both `charon` and `charon-driver`. `target/release/charon` SHA256 equals `bin/charon` (`b2b096…2310c`), but it is a separate regular file/inode. `target/release/charon-driver` is 387,575,256 bytes, SHA256 `4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938`.
- The existing `bin-charon-driver` release fingerprint records features `default,rustc`, empty rustflags, the release profile hash, and a compiled dependency set; its corrected SHA256 is recorded in `source-hashes.txt`. The package has no `.cargo/config` found within the inspected repository depth and no custom `[profile.*]` section or `build.rs`; `--release` is the standard Cargo release profile.
- The `charon` wrapper computes `driver_path` as a sibling of `current_exe`. Therefore the relocated build should run `<candidate>/charon/target/release/charon`, whose sibling driver is the rebuilt `<candidate>/charon/target/release/charon-driver`; do not run the original `bin/charon` for the candidate driver.
- Cargo registry is 1.3G; git checkouts for the locked git dependencies exist. The existing target has compiled library artifacts. Reuse from a relocated clone is not yet proven: `target/release/charon-driver.d` contains absolute paths under the original workspace, so Cargo may rebuild some workspace crates. No cargo dry-run/build was run. This is the main cache uncertainty.

## Proposed smallest build command and caps (not launched)

Use an isolated source tree archived from the pinned commit, and a separate ordinary copy of the 2.2G `charon/target` (no shared inodes or edits to the original tree). Preserve the wrapper and driver as siblings in the copied target. Build only the driver target, offline and locked:

```sh
cd <candidate>/charon
CARGO_TARGET_DIR=<candidate>/charon/target \
  cargo build --manifest-path <candidate>/charon/Cargo.toml \
  --release --offline --locked --jobs 1 --bin charon-driver
```

Run that build in its own user systemd scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Expected work is compilation of the changed Charon driver and any workspace dependency whose copied Cargo fingerprint is stale; no cold build is authorized by this preflight. If the cloned-cache attempt resolves to a broad/cold dependency rebuild, stop before launching it and report the cache miss for lead review. The current target already has the `charon` wrapper executable, and only `translate/get_mir.rs` needs the diagnostic source change; the source patch/build have not been made.

## Host snapshot

At 2026-10-02 22:13 UTC, host reported 62 GiB RAM, 51 GiB available, 5.2 GiB of 8 GiB swap in use, 252 GiB disk free. User systemd scopes listed only `init.scope`; no Cargo/rustc/Charon build process was running. Future build must still capture before/after host reservation and enforce its own no-swap cgroup.

## Scope

This is read-only preflight only. No source or binary was modified; no build, extraction, Charon invocation, or translation was run. The observer is diagnostic-only. A separate authorized run would still need to verify the emitted target DefId/name and compare final translated LLBC against the unchanged capture under an exact AST/output equality gate. `source-hashes.txt` and `preflight.json` identify captured source/fingerprint bytes and distinguish source evidence from the proposed, unbuilt candidate.

The lead supplied a machine-generated 15-file source pin receipt at `lead-audit/remote-source-pins.stdout.json`. `validate_machine_pins.py` regenerates the overlapping pin fields in `preflight.json` and `source-hashes.txt` from that receipt and checks 64-character lowercase hexadecimal format and cross-file equality. The earlier manually transcribed `preflight.json` is preserved under `history/preflight-before-machine-pin-correction.json`; its Rust MIR `syntax.rs` SHA string had an extra character. That transcription mistake came from hand-copying the value rather than reading the machine receipt. The current pin is receipt-derived.
