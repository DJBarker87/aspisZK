# Building the R1 verifier ELF

Source: research commit `07123926e88273271344977a3fdc26d1780cde14`. The build configuration is taken from the receipts `evidence/finish-pair2-20261027/FJd_SBF_default.json` and `FJd_SBF_devnet.json` (with their `receipt.json` files), and the reproduction result from `evidence/native-elfpins-20261028/NCY_ELF_REPRODUCTIONS.md`, `NCY_B001-receipt.json` and, for the default build, `evidence/native-elfscope-20261028/NCR_SOURCE_TO_ELF.md`.

The R1 verifier is the program in `programs/r1-cost-probe`, built from the frozen source at revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; on this branch `crates/`, `programs/r1-cost-probe` and `Cargo.lock` are byte-identical to that revision, and the SHA-256 of `Cargo.lock` is `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. There are two release ELFs from the same source, which differ only in two program identifiers compiled in at build time: the default build, which leaves them unset, and the devnet build, which sets them to the devnet Pool and registry.

## Tools

The build uses `cargo-build-sbf` from Solana release 3.1.13, with platform-tools v1.52 (rustc `1.89.0-dev`, LLVM 20.1.7), target `sbpf-solana-solana`. The executables are identified by hash, because their version output does not report an upstream commit: `cargo-build-sbf` SHA-256 `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c`, and the platform-tools `rustc` SHA-256 `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002`.

## Command

From the repository root, with the dependency sources already vendored in the Cargo home (the build runs offline):

```bash
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS="-C link-arg=--threads=4"
unset RUSTFLAGS CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS

# devnet build only; leave both unset for the default build
export ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs
export ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q

cargo-build-sbf \
  --manifest-path programs/r1-cost-probe/Cargo.toml \
  --sbf-out-dir target/r1-sbf \
  --features pool-adapter,private-leaf-salts \
  --skip-tools-install --offline -j 4 -- --locked
```

The feature `pool-adapter` builds the two-transaction entry points that call the Pool; `private-leaf-salts` selects the compact binary-multiproof proof format of 57,607 bytes, which the verifier crate also enables by default. The program's own manifest pulls in `aspis-r1-cost-probe` with `optimized-terminal` and `program-build`, and the default `custom-heap` feature is on. The receipts of 27 October additionally set `CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3`, which sets the optimisation level of the build scripts (they generate the circle tables) rather than of the program; the reproduction of 28 October did not set it and produced the same ELF.

## Overflow checks

The build uses Cargo's plain release profile. The workspace `Cargo.toml` turns overflow checks on only for the two host-side checker crates `aspis-r1-cert-check` and `aspis-r1-cert-build`, which are not part of the program, and the reproduction explicitly unsets `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS`. The deployed verifier therefore uses wrapping integer arithmetic. The Lean translations on which the 599 verified statements rest were generated with overflow checks on, so that an overflow appears there as an error rather than a wrapped value; carrying the theorems across to the wrapping binary is an open gate, described in [`OPEN-GATES.md`](OPEN-GATES.md) under checked versus wrapping arithmetic.

## Expected results

| Build | Bytes | SHA-256 |
| --- | ---: | --- |
| Default | 1,563,728 | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` |
| Devnet | 1,563,728 | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` |

The devnet ELF is the one deployed on devnet ([`DEVNET-RUN.md`](DEVNET-RUN.md)).

## Reproduction receipt

On 28 October 2026 a fresh, capped build from the frozen source reproduced the devnet ELF exactly (attempt NCY_B001): exit 0, build wall time 28.45 seconds, peak process memory 686,108 KiB, no swap, 1,563,728 bytes, SHA-256 `63ad3e9c…4299`, with all 1,243 pinned source and input files hashed identically before and after the build. The default ELF `f8c0ec72…43d4` was reproduced the same way in the earlier attempt NCR_B003 (exit 0, build wall time 26.32 seconds). The release Pool, `programs/aspis-pool` at `b936275465600469312d1f058cdc91ea2a11f3dc` with features `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`, builds to 345,648 bytes with SHA-256 `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`, reproduced twice on 9 November 2026 (`evidence/legacy-removal-20261109`).

The compiler prints stack-offset diagnostics for some functions while still exiting 0 and producing the exact ELF; they are kept in `NCY_B001-stderr.log` on the research branch. A matching hash establishes that this recipe produces these bytes; it does not establish that the compiler preserved the meaning of the source, which stays a named trust row (P7), nor that the stack diagnostics are unreachable on the deployed path.
