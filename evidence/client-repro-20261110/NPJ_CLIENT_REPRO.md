# NPJ_: reproduction of the devnet proving client devnet_spend 77e7e541

Date 2026-11-10. Stream A job NPJ_. Build host nuc (100.108.41.90), workspace
/home/dombarker/project-offloads/codex-cx-client-20261110. Nothing was written on the
host outside that workspace. Nothing was pushed.

## Result

The binary that proved both devnet runs (NDZ 2026-10-29, NPC 2026-11-10),
devnet_spend SHA256 77e7e541378baa655ba8ebd47052e67a145807392e03d7ce48d6a4bb13ca8289,
was rebuilt byte for byte from revision dfa35acd8390aea176c13710d320d041332b320a with
the recorded command and rustc 1.94.1. All 35 ELF sections are identical (attempt 4,
host/NPJ_attempt4.sections).

Reproduction needs the original absolute source path. A build from any other
directory gives a different binary, as explained under "Why attempts 2 and 3 differ".
The recipe below therefore names that path.

## Reference binary

- The image is sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a
  (tag aspis-ndz-writer:20261029, created 2026-10-29T10:37:48Z, amd64). It was read on
  the Mac with `docker create` and `docker cp :/opt/aspis/devnet_spend`, and the
  container was then removed. The extracted file is NPJ_devnet_spend.ref. It is
  2,496,944 bytes, so it is committed here, under the 20 MB limit.
- Its SHA256 is 77e7e541...8289, equal to the value in NDZ_WRITER_READINESS.json and
  NPC_DEVNET_RESULT.md.
- `file` reports: ELF 64-bit LSB pie executable, x86-64, dynamically linked, interpreter
  /lib64/ld-linux-x86-64.so.2, for GNU/Linux 3.2.0, BuildID[sha1]=c7d3b43ba26e292c29727715b942cd05cd2bcc99,
  not stripped.
- Embedded toolchain strings are `rustc version 1.94.1 (e408947bf 2026-03-25)`, std paths
  `/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1/...`, and `GCC: (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0`.
- The host build output it was copied from still exists, read-only, at
  codex-cx-devnet-rehearse-20261029/NDZ_native-target/release/devnet_spend. That file is
  also 77e7e541 (2,496,944 bytes, mtime 2026-10-29T10:22:57Z), and it matches
  deps/devnet_spend-2840a964ba3a712c. This closes CLIENT_REVISION gap 2(c): the image's
  COPY source is the host NDZ build.

## Source identity

- The original NDZ_src (689 files) was hashed in place with `git hash-object`, read-only.
  Every file equals its blob at dfa35acd, with 0 mismatches. The trees it contains are
  complete at dfa35acd: tools/r1-cost-probe 11/11 files, crates 405/405,
  programs/aspis-pool 28/28, programs/aspis-registry 7/7, and
  docs/research/v8-r0-zk-20261009/z4 169/169. The rest are the needed parts of
  docs/research/v8-r0-zk-20261009 (c3, refine) and the root Cargo.toml/Cargo.lock.
  The blob list is in host/NPJ_ndz_src_blobs.txt.
- The rebuild source was `git archive dfa35acd` of exactly those 689 paths. The archive
  SHA256 is d6de0d0cacd6c6751f97acb58767883ca62c8faa8c2f24e27f93009fd760170a.
- Tree hashes at dfa35acd:

| Path | Tree/blob at dfa35acd | Same at 4bb3b3f? |
| --- | --- | --- |
| tools/r1-cost-probe | 8269965730ed86bf74d1b6aad5c1c7b00aece4b4 | no (4bb3b3f: 32981bc2) |
| crates | 9c52e6b936c8c774c1238973f4acd47460c4afba | yes |
| programs/aspis-pool | 480e2c487312d95e7bcb73612c6dfdd202904c39 | yes (b936275: bf9ea55d, differs) |
| programs/aspis-registry | 712063220888d6714762df7f3f622d2e556c2a2a | yes |
| docs/research/v8-r0-zk-20261009/z4 | 21cf8e2acc6f85a5298dfa10d5b74b71b887ac8d | yes |
| Cargo.lock (root) | 8b19d7e9f605071965661b125310d76ce6409740 (sha256 5782e6a3...ba22ef) | yes |
| tools/r1-cost-probe/Cargo.lock | a056d6f8adcf17bfa24248bf252c57415561f75b (sha256 08de51ef...57b3f9) | yes |
| Cargo.toml (root) | bdc6be47354b7f837665c1aaf49a94b5ed102bbf | yes |

## Recipe (reproduces 77e7e541)

- Toolchain: rustup stable-x86_64-unknown-linux-gnu, rustc 1.94.1 (e408947bf 2026-03-25),
  cargo 1.94.1 (29ea6fb6a 2026-03-24), LLVM 21.1.8. It was already installed on the host;
  nothing was installed. The linker is the system cc, gcc 13.3.0-6ubuntu2~24.04.1 on
  Ubuntu 24.04 with libc6-dev 2.39-0ubuntu8.9, driving rust-lld.
- Registry: the host's existing /home/dombarker/.cargo/registry, mounted read-only. The
  build was `--offline` with `--network none` and made no fetch.
- Source path: the dfa35acd file set must sit at
  /home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_src. The target
  dir was .../NDZ_native-target and the registry was /home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f.
  Attempt 4 got this with a container: an alpine:3.22 image with the host /usr and /etc
  bind-mounted read-only, uid 1000, and the workspace's NDZ_src and target-4 mounted at
  those paths (host/NPJ_build_ctr.sh). No RUSTFLAGS and no wrapper were used.
- Command (cwd .../codex-cx-devnet-rehearse-20261029):
  `cargo build --manifest-path NDZ_src/tools/r1-cost-probe/Cargo.toml --release --locked --offline -j 1 --features r1p-check --bin devnet_spend`.
  The original used `-j 4`. `-j 1` was needed to fit TasksMax=64, because attempt 1 at
  `-j 4` failed when rust-lld could not spawn threads. The job count did not change the
  output.
- Feature set: the dfa35acd Cargo.toml, unchanged, gives the following. These are read
  from the attempt-4 cargo fingerprints.
  - aspis-r1-cu-probe has [private-leaf-salts, r1p-check].
  - aspis-prover has [insecure-spend-fixture, r0].
  - aspis-r1-cost-probe has [default, private-leaf-salts, prover, r1p-check].
  - aspis-statement has [pool-v1-kernel, r0].
  - aspis-pool has [default, no-entrypoint, pair-forest-account-evidence, pair-forest-verifier-lane-invariant-audit].
  - aspis-registry has [default, no-entrypoint].

  insecure-spend-fixture is hard-coded in tools/r1-cost-probe/Cargo.toml and
  crates/aspis-r1-cost-probe/Cargo.toml at dfa35acd. It cannot be switched off without
  changing source, so no with/without variation was run. The reproduced binary is the
  one with the feature on.

## Attempts

The cap for every attempt was a systemd-run --user scope with MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Attempt 4 also had docker --memory 8g,
--memory-swap 8g and --pids-limit 64. The budget was 1800 s, build class. Fewer than 6
scopes were running host-wide, and the host had 57 GB or more of free disk. All
attempts used rustc 1.94.1 and the same source and features.

| # | Path layout | Jobs | Exit | Wall | Max RSS KiB | Swap | Output SHA256 | Sections differing from 77e7e541 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | workspace path, RUSTFLAGS --remap-path-prefix to the NDZ paths | 4 | 101 | 0:02.76 | 353972 | 0 | none (rust-lld "Resource temporarily unavailable", the TasksMax limit) | n/a |
| 2 | as 1 | 1 | 0 | 4:26.84 | 641404 | 0 | d8271c2833e4d34a56170cf2fc134b6568dec486adae1c656877a45108075a5e | .text .rodata .data.rel.ro .eh_frame .eh_frame_hdr .gcc_except_table .symtab .strtab .rela.dyn .rela.plt .got.plt .dynamic .relro_padding .note.gnu.build-id (14 of 35) |
| 3 | workspace path, RUSTC_WRAPPER appending the same remap (no RUSTFLAGS) | 1 | 0 | 5:27.60 | 643884 | 0 | d8271c28... (identical to attempt 2) | same 14 |
| 4 | container, workspace mounted at the original absolute NDZ paths, no remap | 1 | 0 | 6:06.17 | 648140 | 0 | **77e7e541378baa655ba8ebd47052e67a145807392e03d7ce48d6a4bb13ca8289** | none (35/35 identical) |

Attempt 2's first launch, tied to an ssh session, was stopped and relaunched detached.
Its partial log is host/NPJ_attempt2-aborted-nondetached.log. Attempt 4's first launch
used a busybox base, which could not exec the host bash (busybox /lib64 is a symlink).
No build ran in it (host/NPJ_attempt4-busybox-noexec.outer). The lead set attempt 4 as
the last attempt.

## Why attempts 2 and 3 differ

The remap made the embedded path strings equal: 34 occurrences of the NDZ path appear
in both binaries. The .rodata of attempt 2 has the same size as the reference and holds
the same strings in a different order. All mangled symbols from registry crates
(solana_pubkey, curve25519_dalek and others) carry the same hashes as the reference.
Every aspis path-dependency symbol carries a different hash.

tools/r1-cost-probe is its own `[workspace]`, so crates/, programs/ and docs/research/... are
path packages outside the workspace root. The explanation consistent with these
observations is that cargo's -C metadata, and therefore the stable crate ids, symbol
hashes and code layout, depends on their absolute source path. Attempts 2 and 3 agree
with each other although their RUSTFLAGS differ, and attempt 4 matches the reference.
Both facts fit that explanation. So 77e7e541 is a function of the dfa35acd file set
*and* the build directory.

## Proposed pin line for the client

> Client: devnet_spend SHA256 77e7e541378baa655ba8ebd47052e67a145807392e03d7ce48d6a4bb13ca8289 = tools/r1-cost-probe at dfa35acd (tree 8269965730ed), bin devnet_spend, `--release --locked --offline --features r1p-check` (resolved: aspis-prover [r0, insecure-spend-fixture]; aspis-r1-cost-probe [prover, r1p-check, private-leaf-salts]; aspis-statement [r0, pool-v1-kernel]; aspis-pool [no-entrypoint, pair-forest-account-evidence, pair-forest-verifier-lane-invariant-audit]; aspis-registry [no-entrypoint]), rustc 1.94.1 (e408947bf 2026-03-25) x86_64-unknown-linux-gnu with Ubuntu 24.04 gcc 13.3.0-6ubuntu2~24.04.1, lock tools/r1-cost-probe/Cargo.lock a056d6f8, linking crates/ at tree 9c52e6b9 (identical to 4bb3b3f), programs/aspis-registry 71206322 (identical to 4bb3b3f), docs/research/v8-r0-zk-20261009/z4 21cf8e2a (identical to 4bb3b3f) and programs/aspis-pool at tree 480e2c48 (the 4bb3b3f Pool, NOT b936275's bf9ea55d); source rooted at /home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_src (path-dependent build). Reproduced byte-for-byte by NPJ_ attempt 4.

## What this does and does not establish

- Established: binary 77e7e541 equals the build of the dfa35acd file set under the recipe
  above. The image's copy equals the host build. The source tree of the original build
  was dfa35acd, which closes gaps 2(a), (c) and (e) of CLIENT_REVISION.md as far as the
  binary goes.
- Not changed, and still findings for the pin:
  - The client links Pool tree 480e2c48, not the b936275 Pool (bf9ea55d) that NPC
    deployed.
  - tools/r1-cost-probe is dfa35acd's tree, not 4bb3b3f's.
  - insecure-spend-fixture is on.
  - The devnet runs executed this binary under amd64 emulation on the Mac.

  The D1084 one-model pin as written ("crates, programs/r1-cost-probe and Cargo.lock at
  4bb3b3f with programs/aspis-pool at b936275") does not describe this binary. The pin
  must be amended along the lines above, or the model must justify the difference.
- No soundness, privacy or model-refinement claim follows from this reproduction.

Target not yet established.
