# Authenticated tx2 focused native gate

This run exercises the native strict and authenticated tx2 entrypoints on one
deterministic, insecure masked S2 fixture. It does not establish production
checkpoint provenance or any protocol security claim.

The successful source revision recorded by the NUC runner was
`7742957648c33cf045eb6a672e7c7cc796b61087+auth-tx2-gate-20261013+cff8d46181a0125bb5fa60cacc2b0cbd471a903bfbb77eedf346d6391e7441a6`.
The exact input hashes are in `source-manifest.json`; that manifest records the
three synced native-target files and their unchanged dependencies. The adapter
source hash is also recorded there but was not needed by this native example.

The focused command ran on `dombarker@100.108.41.90` (`nuc`) in the
`aspis-100bit-path-20261013` checkout:

```sh
cargo run --release --locked --offline \
  --manifest-path crates/aspis-r1-cost-probe/Cargo.toml \
  --example authenticated_tx2_gate --features prover
```

The command ran in a systemd user scope with `MemoryHigh=4G`, `MemoryMax=6G`,
and `MemorySwapMax=0`. The NUC resource receipt records exit 0, 9.01 seconds,
323,366,912 bytes sampled aggregate peak RSS, 221,655,040 bytes cgroup memory
peak, and zero cgroup swap. It reported: strict/authenticated acceptance and
sorted trace equality; proof 122,231 bytes, public 1,880 bytes, checkpoint
1,768 bytes, and 9,253 trace entries. The unchanged checkpoint rejected a
mutated proof and public. A first query M31 changed to `0xffffffff` was rejected
by authenticated tx2 as `Checkpoint` before trace-producing arithmetic, while
strict tx2 rejected it as `Parse`. Six checkpoint-byte mutations were rejected.

The earlier capped compile attempt `auth-tx2-gate` is retained with exit 101
and its full log. It exposed a source-sync path mistake (the verifier source
was copied to the crate root rather than `src/`); it stopped in 0.50 seconds
without running the gate. The corrected retry has its own run directory and
resource receipt. Both attempts and source manifests are retained under
`remote-evidence/`.
