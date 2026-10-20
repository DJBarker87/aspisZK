# Config-driven R1 devnet commands

Run from this worktree and the retained Linux task workspace. No wallet key,
ELF, proof binary or nonce ledger belongs in git. Keep every task key on the
host, directory 0700 and files 0600, including loader buffers after failures.
The [report](REPORT.md) distinguishes executed phases from pending phases.

Host: `dombarker@100.108.41.90`; task:
`/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
Public config: [r1-devnet.template.json](../../config/r1-devnet.template.json).
The payer is `Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD`.
The config has paths and public identities, never key material. The scripts
resolve signer files from the host's retained `keys/` directory.

## Admission and source preparation

The corrected default ELF pin is `dfc2a91a…`, devnet ELF `fb2fc048…`;
`f11e40b4…` is Stage2.llbc. The corrected gate passed. Do not repeat the
unchanged SBF verifier build; its `.text`/two-slot identity audit is retained.

For a new workspace, synchronize tracked sources and tooling, preserving its
compiled cache and keys. From this worktree:

```sh
git ls-files crates programs tools/r1-cost-probe tools/r1-buffer-carrier \
  Cargo.toml Cargo.lock > /tmp/cx-devnet3-source-files.txt
rsync -a --files-from=/tmp/cx-devnet3-source-files.txt ./ \
  dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020/src/
scp scripts/r1_devnet_{receipt.sh,rpc.py,release_gate.py,deploy_paced.py,spend.py,collect.py,carrier_build.sh} \
  config/r1-devnet.template.json \
  dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020/
```

Use a new receipt directory and unit name for every attempt. Before each
large job, inspect populated scopes and ensure aggregate MemoryMax remains
below 55 GiB; preserve that inspection in receipts:

```sh
cd /home/dombarker/project-offloads/codex-cx-devnet-20261020
systemctl --user list-units --type=scope --state=running --no-pager
systemctl --user show '*.scope' -p Id -p MemoryMax -p MemoryCurrent -p MemorySwapMax
```

## Optimized host driver and separate carrier

Expected time is compilation only. The driver feature enables the actual
retrying prover with P_R1, fresh OS attempt secrets and a durable nonce store.
The carrier is a separate bounded signed-write program; it does not modify
the frozen verifier. Its artifact is pinned in the public config.

```sh
systemd-run --user --scope --unit=cx-devnet3-driver-new \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/driver-new SOURCE_REVISION \
  'Optimized driver compilation; no proof execution' \
  env CARGO_TARGET_DIR="$PWD/native-target" \
  /home/dombarker/.cargo/bin/cargo build \
  --manifest-path src/tools/r1-cost-probe/Cargo.toml \
  --release --offline --locked -j 4 --features r1p-check --bin devnet_spend

systemd-run --user --scope --unit=cx-devnet3-carrier-new \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/carrier-new SOURCE_REVISION \
  'Optimized carrier SBF compilation; no proving' bash r1_devnet_carrier_build.sh
```

The receipt wrapper records native
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. SBF invokes rust-lld directly and
uses `-C link-arg=--threads=4` instead. Each receipt records command, source
revision, exit, wall, peak RSS, swaps and cgroup limits/peak. No Lean runs.

## Deploy the pinned artifacts

Deployment order is verifier, Pool, registry, carrier to fit transient rent.
The first CLI attempt exhausted retries; the paced driver repairs only bytes
that differ in the retained buffer. Loader writes use 900 bytes: a 3,763-byte
loader instruction failed simulation. This loader limit is independent of
3,763-byte uploads to the separate proof carrier.

```sh
systemd-run --user --scope --unit=cx-devnet3-deploy-paced-new \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/deploy-paced-new SOURCE_REVISION \
  'Paced RPC deployment and byte readback; no proving' \
  python3 r1_devnet_deploy_paced.py r1-devnet.template.json receipts/deploy-paced \
  verifier pool registry carrier
```

Each role uses `keys/ROLE.json` and `keys/ROLE-deploy-buffer.json`. Never
regenerate an existing identity or remove a failed buffer key. The driver
checks the full buffer and ProgramData payload against the pinned ELF. Only
then does it make verifier/registry loader deployments immutable, as required
by Registry V2. All keys remain retained. A role that already exists causes
a stop for readback inspection, not an automatic upgrade; pass only the
remaining roles when resuming.

## Initialize and spend

Expected time is RPC finality, then the named P_R1 check/proof generation,
then 16 proof uploads plus one statement upload, stage 1 and Pool settlement
for each operation. This is deliberately a fixture-witness demonstration;
it is not a private wallet UX. Keys and nonce stores remain host-only.

```sh
systemd-run --user --scope --unit=cx-devnet3-spend-new \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/spend-new SOURCE_REVISION \
  'RPC setup; optimized retrying P_R1 proof; uploads; tx1; Pool tx2; negative checks' \
  python3 r1_devnet_spend.py r1-devnet.template.json receipts/spend
```

The optional `--mint-only` flag completes just the independent mint/source/
destination setup. Resume the same receipt directory without that flag to
reuse the finalized setup and continue, without a second mint-to operation.

The script creates the devnet SPL mint, source/destination accounts, registry
release, master, eight lanes and vault, deposits two spendable notes and
creates a forest checkpoint. It reconstructs the historical witness from
those deposits and checks it against the finalized anchor; it reads the live
output lane for each proof. Separate verifier-owned zero checkpoints are
created through System Program. Proof/statement buffers are read-only during
verification. The compact proof buffer contains candidate-afterstate bytes
followed by the proof; the statement is exact ASF8. The carrier requires its
buffer key to sign every bounded upload. At most four disjoint upload ranges
are in flight, and all must finalize before full byte readback and stage 1.

The sender simulates each transaction, records each signed attempt before
submission, queries history until finalized or demonstrably expired, and only
then re-signs with a fresh blockhash (maximum three attempts). Finalized
metadata supplies CU, fees and slot. A prior incomplete named transaction
requires inspection before resumption. Existing completed names are reused;
never blindly start a second spend over changed live state.

The negative checks send a fresh-blockhash replay and a mutated proof with a
fresh zero checkpoint, recording finalized errors and logs. The mutated
header byte is restored afterward. Readbacks include marker, lane, vault,
destination token account and verifier checkpoint.

## Collect metadata and export evidence

```sh
systemd-run --user --scope --unit=cx-devnet3-collect-new \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/collect-new SOURCE_REVISION \
  'Read-only finalized transaction metadata; no proving' \
  python3 r1_devnet_collect.py r1-devnet.template.json receipts/spend receipts/spend-metadata
```

Use `--histories-only` with the whole receipt root to inventory all loader
buffer signatures without fetching every loader-write transaction. Optional
`--loader-writes` also fetches their complete metadata.

The collector incrementally fetches missing finalized metadata and preserves
signature, explorer link, slot, CU, fee, error and logs without embedding ELF
upload bytes. Copy only public receipts; exclude `*-proof-private/`, binary
files, nonce ledgers and every key. Keep old failed-attempt receipts intact.
