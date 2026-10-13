# 100-bit spend path: verifier-fit evidence

This is a mechanical inventory of the copied NUC receipts under
[`evidence/latest/`](evidence/latest/). It records observed verifier costs and
fixture checks only. It does not establish settlement behavior, privacy,
soundness, or release-gate closure.

Evidence was copied read-only from
`dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-100bit-path-20261013/results/100bit-path-20261013/`.
[`evidence/latest/INCLUDED-PATHS.txt`](evidence/latest/INCLUDED-PATHS.txt) lists
the exact copied paths. The copy includes JSON, logs, source manifests, driver
hashes, stack-audit JSON, fixture hash metadata, and measurements. It excludes
proof/public binary fixtures, ELF files, keys and payer files, symbols, and
disassembly.

## Staged S2 diagnostic costs

These are one-run transfer diagnostics at `k=10`, with completion recorded by
the diagnostic receipt. They are useful for comparing the staged verifier
changes; the acceptance measurements below are the capped five-run results.

| Stage | tx1 CU | tx2 CU | Source manifest SHA-256 | Stack audit JSON SHA-256 | Measured ELF SHA-256 | Stack audit result |
| --- | ---: | ---: | --- | --- | --- | --- |
| pairing | 1,761,551 | 1,518,138 | `a7c365534f43f5c508adf4d5b598d5af9059d0cfe74d0f95eff9bc6a4932b16c` | `cd93d2623de93cb1a71e8d4f4760d3f67e7297408aa8eea68de09ac614baee51` | `9f0ea93e3aea66cf47d5561893ead22203d7cba4b4f2d3d4abeb60b3aa4d5004` | 0 reachable diagnostics; 34 absent diagnostic functions |
| terminal | 1,523,042 | 1,518,138 | `cd609c835f17d17fae4eb88fd8f21c7702d2c5d76bb9036d2946a507b7dd151b` | `ca060a68b03c5547b7e541b3621e7a2fcd4c993894d2dd39d7ab7e6e0f67bc21` | `2db3d9c677e740f23a5e6bc3a4eb0fbd965e3cb5c218098403a0e2207d026985` | 0 reachable diagnostics; 34 absent diagnostic functions |
| rho-clean | 1,411,984 | 1,379,425 | `13650c67bae5f0cadf511241e6433cbade00156f22a7881a924dcb2f2ddf2850` | `717370268070488cf7b859516a901441beb5836f49d32e3ba73c2b311f6165dd` | `86048cd4daeed8ef86d11f1ac4944a32c0685a8c4a13070f97c0162c70b5ee5f` | 0 reachable diagnostics; 34 absent diagnostic functions |
| geometry-dots | 1,331,527 | 1,282,676 | `2c2bf97c3ee5db2e58c62a7902d9a3d1de6eb8752f376e08e607716d5db5ebe1` | `7a4e72af83beea1abed42b04e0013fd5103fbabb301f00a6b300e3651b48717a` | `54bb266bab5d4d2ee5492228207cfeabfb276e3b92c160a02d986aee55aeabb1` | 0 reachable diagnostics; 34 absent diagnostic functions |
| d18 | 1,331,210 | 1,281,989 | `f75e70d832444fd562d3ffb000f37e2f0b1c06f7940a2334f04457011e17e8be` | `0677901431fef58a987dffc4be65436e1e011f938c2a57c04ce7f8f01d7174a3` | `48857d754accece121046c5e0ceaa79d49fbbe22e89f1bdda55d08f66ef84a9a` | 0 reachable diagnostics; 34 absent diagnostic functions |
| fast-accumulator (rejected) | 1,341,002 | 1,294,080 | `2fb031f563182ef6cb96ce39a146f83e363b8584f7764075e6e045a3abd2bfb9` | `fe6aaf69cc9d15b02938197b927a234f4756bbc2d2627d2845f022e0aa372eb7` | `3c20383b54fdec3fe9520e9dea95ef52e7231a45cee8b6f2f06de98842833eff` | 0 reachable diagnostics; 34 absent diagnostic functions |

Every stage source revision has the common base
`7742957648c33cf045eb6a672e7c7cc796b61087` and the matching stage label plus
the manifest SHA shown above. The exact revision strings, commands, exits,
resource peaks, and caps are retained in the `*-sbf.json`,
`*-diagnostic.json`, `*-stack.json`, and associated log receipts. Each reported
stage build, diagnostic, and stack-audit receipt has exit status 0 and records
`MemoryHigh=4294967296`, `MemoryMax=6442450944`, and `MemorySwapMax=0`.
The exact stage commands were `cargo build-sbf --manifest-path
programs/r1-cost-probe/Cargo.toml --sbf-out-dir
<stage>/bin -- --locked -j 2` and the recorded release
`aspis-r1-cu-probe diagnostic <stage ELF> <stage>/S2 transfer 10` command.

The `fast-accumulator` diagnostic is 9,792 CU above d18 in tx1 and 12,091 CU
above d18 in tx2. The lead rejected that wiring and reverted it after the
stage. The accumulator helper is absent from the selected D18 source; its
rejected change is preserved only in [`rejected-accumulator.patch`](rejected-accumulator.patch).
The explicit 368-file D18 source snapshot is archived at
[`evidence/d18-selected-source.tar`](evidence/d18-selected-source.tar), with
hashes and verification details in
[`evidence/d18-selected-source-README.md`](evidence/d18-selected-source-README.md).
The d18 ELF, hash
`48857d754accece121046c5e0ceaa79d49fbbe22e89f1bdda55d08f66ef84a9a`, is the
one used for the acceptance receipts below.

## Capped S2 acceptance runs

The d18 transfer and withdrawal acceptance commands each ran under a separate
recorded systemd scope with a 4 GiB high limit, 6 GiB hard limit, and no swap.
Each command used `aspis-r1-cu-probe acceptance <d18 ELF>
results/100bit-path-20261013/d18-native/S2 <fixture> 10`, with the exact
executable path recorded in its receipt. Runtime receipts record Agave 4.2.1,
LiteSVM 0.16.0, a 262,144-byte heap, and a 1,400,000 CU instruction limit.

All five runs for each transaction completed, reported no execution error,
used unchanged proof/public bytes, and used the same d18 ELF hash. Transaction
2 used the checkpoint produced by transaction 1 in that run.

| Fixture | Transaction | Verifier CU (each of 5 runs) | Whole transaction CU (each of 5 runs) | Completed |
| --- | ---: | ---: | ---: | --- |
| transfer | 1 | 1,331,210 | 1,331,566 | 5/5 |
| transfer | 2 | 1,281,989 | 1,282,345 | 5/5 |
| withdrawal | 1 | 1,329,963 | 1,330,319 | 5/5 |
| withdrawal | 2 | 1,281,949 | 1,282,305 | 5/5 |

The two acceptance scope receipts have exit status 0. Their S2 summary JSONs
also record `both_transactions_completed_all_runs=true`. Individual run files
preserve every CU value, execution result, checkpoint hash/origin, proof hash,
runtime config, and phase markers.

## Native dense-trace and mutation evidence

The d18 native gate ran S1 first, then S2, using the recorded
`cargo run --release --locked -p aspis-r1-cost-probe --features
prover,optimized-terminal --example native_gate -- <S1|S2> <fresh output>`
commands. Both receipts exited 0. The gate reports native and dense acceptance,
exact trace agreement, checkpoint roundtrip, and mutation rejection for each
transfer and withdrawal fixture.

| Variant | Fixture | Proof bytes / SHA-256 | Public bytes / SHA-256 | Trace count / bytes / SHA-256 | Rejected mutations |
| --- | --- | --- | --- | --- | ---: |
| S1 | transfer | 95,735 / `51ef2a43166b635cd2a4f39702a7358f86733fb42076c0b640f116907f0c572b` | 1,880 / `d2241c5432fa3d5b34084c06e9c3f510cc61542a793287aad471287563761557` | 20,465 / 777,670 / `3e52a79fd9873ed22989deed009d9e66f6321663161e428a3e6cf9a401a53b46` | 1,164 |
| S1 | withdrawal | 95,735 / `9882201e38ac9ada74353002a914b24304a39d5c054ffb97e2495856a0c328db` | 1,880 / `aacd276edc3cdfedfb8bcba5ebb443305b6c8be72a4262704181fd2b6ffaac01` | 20,465 / 777,670 / `24e39c8d553398c35c89a1818da960178832e081eb83ca46272439e189f18010` | 1,164 |
| S2 | transfer | 122,231 / `eb44b2d0f938cf49cd45ac4f6266dc3ee6d4ec30452cdb5e8e02af3422401c1d` | 1,880 / `d2241c5432fa3d5b34084c06e9c3f510cc61542a793287aad471287563761557` | 10,699 / 406,562 / `52b233f6ae0a05604ea8aabd3d407d20b1d191d9c54a5b4ade1976f48f4f0e26` | 832 |
| S2 | withdrawal | 122,231 / `b19059ce2eecad963bde2416fee69d3447f7098356713907414a79f7c16270fe` | 1,880 / `aacd276edc3cdfedfb8bcba5ebb443305b6c8be72a4262704181fd2b6ffaac01` | 10,699 / 406,562 / `5a0dbf259cd2356e16cab30582533f0723c440962000e83e25023e9fa1573cf0` | 832 |

The S1/S2 native equivalence-test receipt is
`d18-native.json`; it records exit status 0 for the release
`transport_equivalence` and `weights_equivalence` tests with
`prover,optimized-terminal`. Native gate and mutation JSONs are under
`evidence/latest/results/100bit-path-20261013/d18-native/{S1,S2}/`.

These results support only the observed fit of this verifier candidate and
fixtures within the recorded 1.4M-CU two-transaction test setup.
