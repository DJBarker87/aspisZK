# Deployment IDs implementation and release gates — 20 October 2026

**Result: PASS** for the same-source identity gate and all requested standing
gates on the new default ELF.

Source: branch `codex/cx-ids-20261020`, implementation `731018bdc`, base
`410d307d0`. Host workspace:
`dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-ids-20261020`.
No deployment or funding transaction is part of this task; keys remain on
host. No executable artifact or private key is committed. No Lean ran;
`#print axioms` is N/A throughout.

## Same-source identity gate: PASS

The named input sections merge into `.rodata`. Both final ELFs are
1,406,160 bytes. Their section tables are equal; `.text` starts at file
byte 288 (`0x120`), length 1,368,968 (`0x14e388`), and `cmp` exits 0.
The complete files differ at 63 bytes, all within these two slots:

| ID | Final section | Section offset | File offset | Length |
|---|---|---:|---:|---:|
| Pool | `.rodata` | 0 | 1,369,256 (`0x14e4a8`) | 32 |
| Registry | `.rodata` | 32 | 1,369,288 (`0x14e4c8`) | 32 |

`identity.py` checks uniqueness of both default byte arrays, decodes the
expected devnet IDs independently, and proves that replacing exactly the two
slots reconstructs the **whole** devnet file. The unchanged byte among the
64 slot bytes explains the count of 63. `receipts/identity/` retains
`llvm-objdump -h`, `cmp` exit and the machine-readable audit.

The prior ELF `8cf8d84e…` is superseded by this implementation, not reproduced:
its instruction-immediate obstruction remains valid. New default/devnet
identity is the amended gate. This job does not include the other worker's
stage-2 refactor or claim its final combined freeze.

## Pins

| Build | SHA-256 | Bytes |
|---|---|---:|
| Default | `b324b4cd9b560124f61bf7c4a08a82cd2df1502113cd0b5d6d5249b81ebde019` | 1,406,160 |
| Devnet | `6c8a200a16bff944b9ca3470ab78099e379531d6e8e16bffc95ef2c11b68df68` | 1,406,160 |

`.rodata` starts at 1,369,256, length 20,624. `.data.rel.ro` starts at
1,389,880, length 4,832. Complete inventories are in `identity.json`.
`artifacts-sha256.txt` additionally pins the complete unstripped links,
unchanged Pool/registry ELFs and reused optimized LiteSVM measurement driver.
The driver is copied from the format-adoption job; fixtures are its six
retained compact proofs, not freshly generated proofs. Every runtime record
pins the new default verifier hash. Statements and proof hashes are retained.

Devnet IDs:
- Pool: `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`
- Registry: `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`

## Six-fixture CU gate: PASS

LiteSVM 0.16.0, TxV1, split 10; unchanged B1 Pool. These are fixture
measurements, not an analytical bound over all admitted proofs.

| Fixture | Stage 1 | B1 | Delta | Settlement | B1 | Delta |
|---|---:|---:|---:|---:|---:|---:|
| transfer-13 | 1,196,046 | 1,199,648 | -3,602 | 1,135,548 | 1,129,757 | +5,791 |
| transfer-255 | 1,198,152 | 1,199,567 | -1,415 | 1,166,591 | 1,161,066 | +5,525 |
| transfer-1023 | 1,192,314 | 1,199,687 | -7,373 | 1,166,336 | 1,160,974 | +5,362 |
| withdrawal-13 | 1,192,444 | 1,198,225 | -5,781 | 1,145,844 | 1,138,950 | +6,894 |
| withdrawal-255 | 1,192,575 | 1,198,264 | -5,689 | 1,175,802 | 1,170,523 | +5,279 |
| withdrawal-1023 | 1,194,056 | 1,198,386 | -4,330 | 1,173,380 | 1,170,263 | +3,117 |

All stage-1 rows are ≤ B1; all settlement rows are ≤ B1 + 10,000.
Against the previous format-adopted verifier, stage 1 is identical and
settlement costs 67 additional CU on every fixture. Each replay accepted
natively (strict and dense) and through the SBF runtime. Full runtime
receipts and per-fixture JSON are retained; no RPC measurements are claimed.

## Standing gates

| Gate | Result |
|---|---|
| Codec | PASS: 1,233 outputs byte-identical to D70; hash and byte count in `verification.json`. |
| Ordered trace | PASS: 583 audit calls equal D70; 1,095 adopted calls equal prior format-adopted trace. Calls, counts and checkpoint bytes compared exactly; repeated-input summaries sorted by input to account for HashMap order. |
| Program/checkpoints | PASS: 34/34 including checkpoint, route, raw-buffer and decoder cases; final source rerun after removing `#[used]`. |
| Pool | PASS: default 87, R1/source-invariant 118, all features 123, v7 candidate 123; each also passes 2 integration tests. |
| Strict stack | PASS: verifier and unchanged Pool. No surviving oversized frame, call overwrite or unparsed diagnostic. Complete linked symbols and relocation targets inspected; stripped and linked executable sections equal. |
| P_R1 retrying prover | PASS: 8/8 accepted, all 8 verified by strict tx1+tx2 and dense; retry loop accepted in 1 attempt and verified strict/dense. |
| Proof-size teeth | PASS: default tx1/strict tx2/authenticated tx2/dense accept; all 28 mutations reject. |

## Build history, resources and reproducibility

The first implementation (`81a3eb859`) used `#[used]`. Its identity gate
passed, but its first CU replay exited 1 with `Incompatible ELF: wrong ABI`.
LLVM emitted SHF_GNU_RETAIN and OSABI 3. Removing `#[used]` at `731018bdc`
keeps the statics live through actual references while restoring OSABI 0.
Both final ELFs load successfully; no header patch or post-link workaround
was applied. The rejected artifacts are retained on the host and pinned in
their original build receipts; `receipts/attempt-gnu-retain/` preserves the
failure and earlier measurements. No unchanged failed build was retried.

All source compilation, native arithmetic and replay ran on the Linux host
in scopes with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Cargo used release/offline/locked, `-j 4`; no large local build ran.
Expected expensive work was compilation, then P_R1 proof generation and
extracted checking (recorded in its receipt), not finite-field elimination.
The initial observed four peer scopes reserved 32 GiB; adding two task
scopes gives 48 GiB, below 55 GiB. Later peer scopes finished;
`reservation-snapshot.txt` records the remaining 8-GiB retry scope.
No peer job was modified. All completed jobs report zero swaps.

Native jobs use `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. SBF calls rust-lld
directly: the inherited native spelling is removed for that invocation and
`CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'` supplies
the same linker thread limit, as in the prior devnet job. Toolchain versions
are recorded in `toolchains.txt` (native Rust 1.94.1; cargo-build-sbf 3.1.13,
platform-tools v1.52, SBF Rust 1.89.0, LLVM 20.1.7).

Final default SBF build: exit 0, 2.44 s, peak RSS 204,100 KiB, zero swaps.
Final devnet build: exit 0, 2.76 s, peak RSS 204,164 KiB, zero swaps.
Build receipts include cgroup peaks, timestamps and exact command/env.
Their launcher revision-label typo is explicitly corrected in
`source-revision-note.txt`; the 628-file manifest independently pins source.
Codec/trace and early Pool runs began before the metadata fix; their input
crates are unchanged between `81a3eb859` and `731018bdc`. The only affected
native gate, program/checkpoints, was rerun on final source. No unrelated
full suite was repeated.

Reproduce using `harness/r1_devnet_build.sh` inside the specified systemd
scope, for `default` then `devnet`, with identical source and the recorded
public ID template. Run `identity.py HOST_DIR` through `capped-run.sh`;
`replay-six.sh` runs the retained fixtures against the default artifact.
`harness/gates.sh` contains the standing native commands;
`harness/strict-stack.py` consumes the complete link, stripped ELF and
compiler log. `verify.py` only checks retained evidence, hashes and thresholds.
Large codec stdout and extracted `.text` binaries stay on the host;
their hashes/lengths replace them here. Runtime JSON, strict-stack audits,
command/resource receipts and source/artifact hashes are committed.

P_R1 receipt: exit 0, 415.941 s wall, peak RSS 588,096 KiB, zero swaps.
Final evidence validation: exit 0, 0.121 s, peak RSS 48,520 KiB, zero swaps.
`verification.json` indexes gate results and resource receipts. Remaining work
is the lead’s combined stage-2 freeze/pin and subsequent deployment; no
formal proof obligation or network deployment is closed by these measurements.
