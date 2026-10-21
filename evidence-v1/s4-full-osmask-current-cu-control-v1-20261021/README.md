# Current-format full-mask proof CU comparison

This source-only packet records one accepted current-format private-transfer example against the frozen default verifier ELF and the combined candidate verifier ELF. It is a single proof result, not a distribution, universal CU bound, or adoption decision.

## Result and CU accounting

The exact same 57,607-byte proof (SHA-256 `42fc1617dbc212ef07f7a5cd4f177d2014530198a2fefa40d25914d79ca46ee8`) and public input (SHA-256 `5b3b4ea275b0f447bdfc69a726b6e42f20d40c54af414feb1832a6a4174c9410`) was accepted in both runs. The original corpus evidence identifies it as OS entropy / `full-mask`; the new measurements explicitly reused it, so their own fixture records correctly say the reused payload's entropy is unknown.

| Measurement | Frozen default | Combined candidate | Difference |
|---|---:|---:|---:|
| R1 stage-1 transaction (`execution.stage1_compute_units`) | 1,196,068 | 1,206,885 | +10,817 |
| Pool settlement transaction (`execution.compute_units`) | 1,139,924 | 1,150,423 | +10,499 |
| Nested selected-verifier CPI in settlement logs | 1,042,510 | 1,053,009 | +10,499 |

The stage-1 and settlement numbers are separate transactions. The nested verifier CPI is a component of the settlement transaction and must not be added to it. Both transactions are below the configured 1,400,000 CU limit. Execution was accepted, with no transaction error, on the same seeded public statement and same loaded pool/registry artifacts.

The verifier ELF pins are default `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` and candidate `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`. Shared Pool ELF SHA-256 is `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`; registry ELF SHA-256 is `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab`.

## Provenance and command

`provenance/original-corpus-provenance.json` binds the corpus inventory row to the original run's `evidence.json`. That evidence says `mask_entropy_option=os`, `mask_mode=full-mask`, entropy source `OS getrandom via StateOnlyAttemptSecrets::generate`, and confirms the submitted proof hash matches the proof hash. The retained inventory-generator source and its hash are included. The proof and public binary inputs are not copied into this source-only packet; their exact hashes and lengths are recorded.

The pinned driver source is unchanged at SHA-256 `7b48182aa1a39a1452e164bf24fc54b896d7ec982b9203aa6bf32e12e8dd86e4`. The isolated driver manifest changes only the executable selection/path wiring needed for this copied workspace; `Cargo.lock` remains SHA-256 `8b4eeda2858edbb6963b50782643bf27fc3299549b2e00521e581566e7f8e409`. The build was offline, release, locked, and `-j1`; its binary SHA-256 is `cfc19b39b5ebfb28bc6f97467eb525f31a40e370cfa067a078dda79f90b26142` (binary omitted).

The two measurement commands in `measure/{default,candidate}/command.json` use the same flags and inputs: transfer success, `--pairs 0 --seed 20001 --split 10 --uniform-lane --tx-version v1 --zeroed-genesis-page --reuse proof.bin public.bin`. The original seed and flags reconstruct the matching public statement; the exact proof/public pair is reused in both runs. Per-run receipts record exit status, process RSS, scope peak, swap, event counters, cgroup limits, and full argv.

The release build ran under `MemoryHigh=768 MiB`, `MemoryMax=1 GiB`, `MemorySwapMax=0`: exit 0, 252.914s, process peak RSS 642,560 KiB, scope peak 805,568,512 bytes, swap 0. Each measured run ran under `MemoryHigh=512 MiB`, `MemoryMax=1 GiB`, `MemorySwapMax=0`; both exited 0, took 0.114s, used 37,868/38,512 KiB peak RSS and 42,602,496/43,118,592 bytes scope peak, with swap 0 and no memory events. Fresh-admission snapshots and reservations are included.

The build wrapper's initial post-build assertion failed because the driver's `--help` usage string omits `--seed` and `--uniform-lane`; the exact pinned source contains parser branches for both, and the successful measurement commands exercised them. The build itself exited 0. This wrapper diagnostic is retained in `build/help.txt` and is not a failed measurement.

## Earlier invalid attempts

`diagnostics/` preserves representative failed attempts, classified as harness/setup failures with no valid CU comparison:

- `old-wire-r18/`: the wrong pre-adoption frozen proof was rejected as “wrong frozen proof.” It is not the current 57,607-byte wire and is excluded from all cost claims.
- `adopt-poolgate-mismatch/`: `pool_gate_adopt` rejected the reused proof/public pair because its locally constructed fixture statement differed. It failed before a measured transaction.
- `current-invalid-pool-gate/`: the earlier native driver used a fixture path that was absent and its attempt had `verifier_completed=false`, `InvalidInstructionData`, and only 696 CU before failure. This is not a successful verifier/settlement measurement.
- `build-manifest-failure/`: an earlier isolated driver manifest failed to parse; no binary or CU result came from that attempt.

These records are kept to prevent them being mistaken for a pass or merged into the valid comparison.

## Key retention

No private-key bytes or binary artifacts are included. Keypair files created by the original proof run and the two LiteSVM runs remain in their original NUC task directories; they were neither read nor deleted by this packaging step. `key-retention.json` records the retained paths. Proof/public inputs are represented only by hashes and sizes here.

## Reproduction/checking

Run `python3 verify_packet.py` from this directory. It checks the pinned source/config/input hashes, original corpus provenance, exact equality of the proof/public identity across the two accepted evidence records, the two CU fields and deltas, and absence of binary/key files from this packet. The check does not rerun the build or measurements.
