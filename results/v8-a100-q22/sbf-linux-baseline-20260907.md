# V8-A100 Linux SBF reachability and matched V7 baseline

Date: 2026-09-07

Source revision: `e8627859856b792b2258d7e262b74d4199d5fc9d`

Execution boundary: a task-owned source export and disposable LiteSVM runtime on
`dombarker@nuc.local`. No RPC, public validator, signing service, deployment, or
live program was used or modified.

## Environment

- OS/architecture: Linux x86_64
- logical CPUs: 22
- physical memory at preflight: 66,698,657,792 bytes total; 63,583,318,016 bytes available
- `systemd-run`: systemd 255
- SBF tool: `solana-cargo-build-sbf 2.3.0`
- platform tools: v1.48, Rust 1.84.1
- local runtime tool: `solana-test-validator 2.3.0` / Agave client
- SBF SDK: `/home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin/platform-tools-sdk/sbf`
- task root: `/home/dombarker/project-offloads/aspis-v8-sbf-baseline-e8627859-20260907-r1`

Every build or harness invocation ran in its own user systemd scope with
`MemorySwapMax=0`. SBF builds used `MemoryHigh=4G`, `MemoryMax=6G`; the cold
release harness used `MemoryHigh=6G`, `MemoryMax=8G`.  The latter configured
cap was not strictly below 8 GiB, but its measured peaks were only 541,352 KiB
(rollover) and 539,436 KiB (same-page), with zero swap.  All later jobs in this
investigation use `MemoryMax` at or below 7G to enforce the user's clarified
per-job ceiling strictly.

## V7 SBF build results

Verifier command (line-wrapped only):

```text
systemd-run --user --wait --collect --pipe \
  --unit=aspis-v8-v7-verifier-e8627859-r4 \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p OOMPolicy=stop \
  /usr/bin/time -v env NO_DNA=1 \
  /home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin/cargo-build-sbf \
  --manifest-path /home/dombarker/project-offloads/aspis-v8-sbf-baseline-e8627859-20260907-r1/source-complete/programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate \
  --arch v0 --offline --skip-tools-install --tools-version v1.48 \
  --sbf-sdk /home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin/platform-tools-sdk/sbf \
  --sbf-out-dir /home/dombarker/project-offloads/aspis-v8-sbf-baseline-e8627859-20260907-r1/sbf-verifier \
  -- --locked
```

- exit status: 0
- wall time: 28.76 seconds
- maximum RSS: 560,840 KiB
- swaps: 0
- verifier ELF: 1,819,432 bytes
- verifier SHA-256: `3247628ca57225e5ca297b549c3aba0db6971c2480710751d1b25d600dfba204`

Pool used the same command shape with manifest `programs/aspis-pool/Cargo.toml`,
output `sbf-pool`, and unit `aspis-v8-v7-pool-e8627859-r1`.

- exit status: 0
- wall time: 26.36 seconds
- maximum RSS: 551,912 KiB
- swaps: 0
- Pool ELF: 536,752 bytes
- Pool SHA-256: `9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d`

## V8 stack diagnostic found during the V7 builds

The platform-tools SBF analyzer emitted these exact diagnostics while compiling
`aspis-core`:

```text
Error: Function ...v8_deep_quotients_reference_wire... Stack offset of 11800 exceeded max offset of 4096 by 7704 bytes, please minimize large stack variables. Estimated function frame size: 11904 bytes. Exceeding the maximum stack offset may cause undefined behavior during execution.

Error: Function ...v8_deep_quotients_optimized_wire... Stack offset of 18048 exceeded max offset of 4096 by 13952 bytes, please minimize large stack variables. Estimated function frame size: 18880 bytes. Exceeding the maximum stack offset may cause undefined behavior during execution.
```

The V7 build still exits zero because neither function is reachable from the V7
entrypoint and both are removed from the final ELF. The pinned SDK's
`llvm-readelf -s aspis_verifier.so | grep -c v8_deep` returned `0`. This makes
the existing V7 artifact safe from these dead functions, but it is a hard
implementation gate for any V8 entrypoint that calls the current optimized
function. It is not a CU result.

A stack-safe V8 kernel should:

1. stop returning the 88-QM31 quotient array by value;
2. derive four fibre points from each selected base point on demand instead of
   materializing 88 `SecureCirclePoint`s;
3. stream the 29-component gamma dots from decoded C1/C2 limbs instead of
   materializing `[[QM31; 29]; 4]` per query;
4. put batch-inversion prefixes/denominators in one explicitly allocated heap
   buffer, or fold quotients in bounded chunks with a measured inversion
   tradeoff; and
5. exclude the slow reference implementation from the SBF target.

After that refactor, the SBF analyzer must show every reachable frame below
4,096 bytes before any CU number is accepted.

## Matched strict-work V7 transaction baseline

The selected `v7-pair-forest-one-tx-candidate` feature includes the default-off
`v7-pair-forest-fixed-canonical-exact-once-audit`.  It serializes the same 641
fixed QM31 values as 10,256 canonical bytes instead of 9,936 packed bytes:
exactly +320 bytes.  Its body without frontiers is therefore 20,268, not the
production packed grammar's 19,948.  Roots, nonces, query records, salts and
frontiers are otherwise copied byte-for-byte.

Harness command shape:

```text
cargo run --release --locked --offline \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml \
  --bin aspis-v7-pair-forest-combined-rejection -- \
  <new-pool.so> <new-verifier.so> <registry.so> <result-double.so> \
  <new-evidence.json> <strict-work-fixture.bin> \
  success 1400000 asq8 <populated-pairs> withdrawal
```

| Shape | Populated pairs | Proof payload | Canonical-audit body | Packed equivalent | Frontier/tree | TxV1 bytes | Total CU | Verifier CPI CU | Pool reported CU |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| withdrawal, same page | 13 | 31,512 | 30,824 | 30,504 | 203 | 1,010 | 1,153,267 | 1,085,276 | 1,153,211 |
| withdrawal, rollover | 255 | 31,460 | 30,772 | 30,452 | 202 | 1,043 | 1,218,981 | 1,084,747 | 1,218,925 |

The harness maximum RSS was 539,436 KiB for same-page and 541,352 KiB for
rollover; both reported zero swaps.

Both transactions accepted with all 35/31/34-bit work checks. The harness
confirmed exact lane, history, nullifier-marker, and token-balance changes;
registry, proof, checkpoint, master, mint, and vault-authority state remained
unchanged as required.

The harness's `proof_bytes` subtracts the 688-byte candidate afterstate from
the payload, so the +320 delta is neither an account header nor Pool framing.
The exact identities are `20268 + 2*203*26 = 30824` and
`20268 + 2*202*26 = 30772`; subtracting the canonical-fixed delta recovers the
packed bodies above.  This resolves the apparent 30,504-byte source mismatch.

Remote evidence identities:

- rollover JSON SHA-256: `7a24cab29def602d17d392f711443aed5436b31d81302af6139f25a4c405f4e4`
- same-page JSON SHA-256: `dbbec1c5304ebd33f2b22f8d917d87b96b8181d5a80403a73e53fd600e4b8799`
- registry ELF SHA-256: `0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b`

The 9-CU increase over the retained 1,218,972-CU rollover record is measured,
not inferred. The current source and newly built ELF hashes differ from that
older evidence, so this file does not call the binaries byte-reproductions of
the historical artifacts.

## Why V8 transaction CU is still unavailable

`aspis-core::v8_a100` and `aspis_core::v8_deep` are library prototypes only.
The repository currently has none of the following:

- a mutually exclusive `v8-a100-cu-probe` verifier feature and entrypoint;
- a complete V8 transcript/relation verifier (the V7 transcript types and
  schedules are hard-coded to q16 and the compact candidate loop);
- q22 Merkle authentication/folding composition using the V8 quotient;
- a V8 pair-forest profile/release binding and dispatch;
- an honest V8 prover fixture for the deterministic Pool statements; or
- V8-aware proof-length/frontier derivation in the pair-forest dispatch and
  LiteSVM harness.

Therefore neither the 1.4M hard gate nor the 1.35M preferred gate has been
measured for V8.

The smallest honest integration sequence is:

1. make the V8 optimized DEEP kernel stack-safe and add an isolated SBF kernel
   probe for parser/direct-schedule/DEEP attribution;
2. implement a complete V8 transcript verifier rather than adapting the V7
   q16 view by casts;
3. generalize the dynamic 208-bit minimal-subtree verifier to q22 and feed the
   authenticated V8 openings into the existing fold/final representation;
4. add a V8 prover/KAT for both a typical and the exact 296-node frontier;
5. add a distinct, default-off V8 pair-forest dispatch feature/binding while
   leaving every production/default V7 route unchanged;
6. parameterize the existing harness's V7 constants and proof-length inversion
   by that V8 descriptor; and
7. rerun verifier-only, same-page, rollover, typical/max-frontier, and strict
   work cases under the same 1.4M TxV1 budget.

## Resolved launch failures

Three pre-compilation failures were retained as operational evidence:

1. A relative manifest under `systemd-run --working-directory=...` resolved
   from the SSH login directory on this host. Resolution: use an absolute
   manifest path.
2. The first full `git archive | ssh tar` stream exceeded the local command
   yield and left an alphabetical partial export with no `programs/` tree.
   Resolution: export the narrow source set into a new `source-complete/`
   directory.
3. That narrow export initially omitted the root workspace member
   `audit/poseidon-pair-probe/program`. Resolution: export every workspace
   member required by root `Cargo.toml`; the succeeding builds used the
   complete set.

None of these failures was a compiler or protocol failure.
