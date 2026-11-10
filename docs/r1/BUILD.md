# Building the programs

This page explains how to build the verifier and the pool from the frozen
source and how to check a build against the programs deployed on devnet. The
verifier is the program in `programs/r1-cost-probe` and the pool is the program
in `programs/aspis-pool`. On this branch `crates/`, `programs/r1-cost-probe` and
`Cargo.lock` are byte-identical to the frozen verifier revision `4bb3b3f`, and
`programs/aspis-pool` to the frozen pool revision `b936275`, so a build from
this checkout is a build of the frozen source.

The verifier has two program identifiers compiled into it, those of the pool
and of the registry it works with. They are set from environment variables at
build time, so one source gives several ELFs that differ only in those
identifiers: a default build that leaves them unset, the release devnet build
that names the pool and registry used in October 2026, and the build deployed
in November 2026, which names the new pool address and the same registry.

## Tools

The build uses `cargo-build-sbf` from Solana release 3.1.13, with
platform-tools v1.52 (rustc `1.89.0-dev`, LLVM 20.1.7) and target
`sbpf-solana-solana`. Because the version output of these executables does not
report an upstream commit, they are identified by hash in the table at the end
of this page.

## Building the verifier

From the repository root, with the dependency sources already vendored in the
Cargo home, since the build runs offline:

```bash
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS="-C link-arg=--threads=4"
unset RUSTFLAGS CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS
unset CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL

# Program identifiers: leave both unset for the default build.
# Release devnet build (October 2026):
export ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs
export ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
# For the verifier deployed in November 2026, use the new pool address instead:
# export ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt

cargo-build-sbf \
  --manifest-path programs/r1-cost-probe/Cargo.toml \
  --sbf-out-dir target/r1-sbf \
  --features pool-adapter,private-leaf-salts \
  --skip-tools-install --offline -j 4 -- --locked
```

The feature `pool-adapter` builds the two-transaction entry points that call
the pool, and `private-leaf-salts` selects the compact binary-multiproof proof
format of 57,607 bytes, which the verifier crate also enables by default. The
program's own manifest pulls in the verifier crate with `optimized-terminal`
and `program-build`, and the default `custom-heap` feature is on.

`CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL` must not be set. It enters
every crate's metadata hash, and so changes symbol hashes and code layout. An
earlier pair of builds that set it to 3 did not reproduce the pins, and a later
audit confirmed that the same recipe with the variable reproduces that mismatch
while the recipe without it reproduces both release ELFs byte for byte, the two
differing from each other in 63 read-only data bytes, all inside the pool and
registry identifier slots.

## Building the pool

The pool is the program in `programs/aspis-pool`, built with the same tools and
the features
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`.
Its exact build command is in the reproduction receipts named at the end of
this page.

## Overflow checks

The build uses Cargo's plain release profile, so the deployed verifier uses
wrapping integer arithmetic. The workspace `Cargo.toml` turns overflow checks on
only for the two host-side checker crates `aspis-r1-cert-check` and
`aspis-r1-cert-build`, which are not part of the program, and the commands above
explicitly unset `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS`. The Lean translations
on which the 599 verified statements rest were generated with overflow checks on,
so that an overflow appears there as an error and not as a wrapped value.
Carrying the theorems across to the wrapping binary needs a proof that no
overflow can occur, and that proof is complete for all 197 definitions in the
theorem's dependencies that execute checked arithmetic. What remains are seven
named places where the count relied on reading the source instead of on a Lean
statement, and they are described in [`OPEN-GATES.md`](OPEN-GATES.md) under
checked versus wrapping arithmetic.

## Checking a build against devnet

A deployed program's bytes can be fetched with the Solana command-line tool and
hashed:

```bash
solana program dump --url devnet GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy verifier.so
head -c 1563728 verifier.so | shasum -a 256   # compare with the November verifier below

solana program dump --url devnet 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt pool.so
head -c 345648 pool.so | shasum -a 256        # compare with the pool below
```

This check was run against devnet on 10 November 2026, and both dumps were
exactly the length of the ELF with matching hashes. The `head -c` is there as a
guard, because a dump holds the whole program-data region and would be longer
than the ELF if the account had been allocated with spare room. The October verifier is at
`CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ` and is checked the same way
against the release devnet ELF.

## Expected results

| Build | Bytes | SHA-256 |
| --- | ---: | --- |
| Verifier, default | 1,563,728 | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` |
| Verifier, release devnet build (October) | 1,563,728 | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` |
| Verifier, November devnet build | 1,563,728 | `2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea` |
| Pool | 345,648 | `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc` |

| Input | SHA-256 |
| --- | --- |
| `Cargo.lock` | `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef` |
| `cargo-build-sbf` | `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c` |
| platform-tools `rustc` | `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002` |

Each of these ELFs has been reproduced from the frozen source. A capped fresh
build reproduced the release devnet ELF exactly, with every pinned source and
input file hashing identically before and after, and the default ELF was
reproduced the same way. The November verifier was built twice with identical
results, alongside a control build that reproduced the release devnet ELF, and
the pool was reproduced twice. The deployed programs and runs are described in
[`DEVNET-RUN.md`](DEVNET-RUN.md).

The compiler prints stack-offset diagnostics for some functions while still
exiting successfully and producing the exact ELF. A matching hash shows that
this recipe produces these bytes. It does not show that the compiler preserved
the meaning of the source, which remains a named trust assumption, or that the
functions with stack diagnostics are unreachable on the deployed path.

## Where this comes from

The build configuration and reproduction receipts are on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch at
commit `07123926e88`, under `evidence/finish-pair2-20261027`,
`evidence/native-elfpins-20261028`, `evidence/native-elfscope-20261028`,
`evidence/l188-20261109` and `evidence/legacy-removal-20261109`; the build of
the November verifier is recorded in `evidence/devnet-frozen-20261109` at commit
`af8f9fd2f9d`. The stack diagnostics are kept in the reproduction logs there.
