# Building the programs

This page explains how to build the verifier, the pool and the upload program
from the pinned source and how to check a build against the programs deployed
on devnet. The verifier is the program in `programs/r1-cost-probe`, the pool
is the program in `programs/aspis-pool`, and the upload program, which holds a
proof while it is written to the chain, is in `programs/aspis-upload`. On this
branch `crates/`, the three program directories, `Cargo.toml` and `Cargo.lock`
are byte-identical to the pinned commit `c7593d23fdc`, apart from the folder
README in `crates/`, so a build from this checkout is a build of the pinned
source. The pool there is unchanged from the earlier pool revision `b936275`.

The pin moved on 11 November 2026. The verifiers deployed in October and on
10 November were built from the earlier pin `4bb3b3f`, and their hashes are
kept in the table of expected results for reference. To rebuild them, check
out that revision and use the same commands.

The verifier has two program identifiers compiled into it, those of the pool
and of the registry it works with. They are set from environment variables at
build time, so one source gives several ELFs that differ only in those
identifiers: a default build that leaves them unset, and the build deployed
on devnet, which names the pool at `37hdATMk…` and the registry that has been
in use since October 2026.

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
# For the verifier deployed on devnet:
export ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt
export ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
# The October verifier, at the earlier pin, used the same registry and the pool
# BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs.

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

## Building the upload program

The upload program has no features and no compiled-in identifiers, and is
built with the same environment:

```bash
cargo-build-sbf \
  --manifest-path programs/aspis-upload/Cargo.toml \
  --sbf-out-dir target/upload-sbf \
  --skip-tools-install --offline -j 4 -- --locked
```

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
overflow can occur. For the previous build that proof is complete for all 197
definitions in the theorem's dependencies that execute checked arithmetic. What
remains there are seven named places where the count relied on reading the
source instead of on a Lean statement, and they are described in
[`OPEN-GATES.md`](OPEN-GATES.md) under checked versus wrapping arithmetic. The
current pin adds one checked subtraction, in the length check of the
instruction that closes a checkpoint, which is guarded by a length test of its
own. It will be counted with the others when the proofs have been recompiled
against the current pin.

## Checking a build against devnet

A deployed program's bytes can be fetched with the Solana command-line tool and
hashed:

```bash
solana program dump --url devnet BLgzrkDiCs4f7bwWrP4EBSNN5nhi2snfoLopxs2X3xNg verifier.so
head -c 1567992 verifier.so | shasum -a 256   # compare with the deployed verifier below

solana program dump --url devnet 9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5 upload.so
head -c 25992 upload.so | shasum -a 256       # compare with the upload program below

solana program dump --url devnet 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt pool.so
head -c 345648 pool.so | shasum -a 256        # compare with the pool below
```

Before the run of 11 November 2026 the bytes of all three programs on devnet
were compared with the built files and matched. The `head -c` is there as a
guard, because a dump holds the whole program-data region and would be longer
than the ELF if the account had been allocated with spare room. The verifier
of 10 November is at `GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy` and the
October verifier at `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ`, and each is
checked the same way against its ELF from the earlier pin.

## Expected results

| Build | Bytes | SHA-256 |
| --- | ---: | --- |
| Verifier, deployed on 11 November | 1,567,992 | `2284239edf238730aa0def62ec06176c364f6cb35cef1934ca18b0df0fbd6278` |
| Verifier, default | 1,567,992 | `5f083ab38e4b5bbe023bffda603a26aa969019a700cb194114625ec448ff6f7f` |
| Upload program | 25,992 | `9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874` |
| Pool | 345,648 | `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc` |
| Earlier pin: verifier, default | 1,563,728 | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` |
| Earlier pin: verifier, October | 1,563,728 | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` |
| Earlier pin: verifier, 10 November | 1,563,728 | `2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea` |

| Input | SHA-256 |
| --- | --- |
| `Cargo.lock` | `7cc53354599b6c1567e23957a8cfd6469ace3e11d85edbbd5f26851b211db7cd` |
| `Cargo.lock` at the earlier pin | `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef` |
| `cargo-build-sbf` | `46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c` |
| platform-tools `rustc` | `d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002` |

Each of these ELFs has been reproduced from its source. The current verifier
and the upload program were each built twice in fresh build directories with
identical results, and the default and deployed verifiers differ only in the
63 bytes of the two identifier slots. The lock file differs from the earlier
one only by the entry for the upload program. At the earlier pin, a capped
fresh build reproduced the October ELF exactly, with every pinned source and
input file hashing identically before and after, and the default ELF was
reproduced the same way. The verifier of 10 November was built twice with
identical results, alongside a control build that reproduced the October ELF,
and the pool was reproduced twice. The deployed programs and runs are described in
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
the verifier of 10 November is recorded in `evidence/devnet-frozen-20261109` at
commit `af8f9fd2f9d`. The builds at the current pin are recorded in
`evidence/prov-p9c-20261110/final` at commit `189492240ed`. The stack diagnostics are kept in the reproduction logs there.
