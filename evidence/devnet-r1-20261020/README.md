# R1 devnet resume commands

The frozen-source devnet build and data-only identity audit pass. Deployment
is blocked by the task/lead decision naming the LLBC hash as the default ELF
pin; see [REPORT.md](REPORT.md). No deploy/init/upload/spend ran.

Source/base: `fa894d83d2f3ad6df34bc8493881c780621d553e`, branch
`codex/cx-devnet3-20261020`. Host task directory:
`/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
[Public config](../../config/r1-devnet.template.json) contains no secrets.
Keys remain on the host (0700 directory, 0600 key files); never copy them
into the repository or remove funded keys. No binary is committed.

## Source preparation and optimized build

Commands below describe the executed run. Receipt directories already exist;
do not repeat an unchanged build. Inspect populated cgroup reservations first
and keep total MemoryMax below the host's 55-GiB safe limit.

From this worktree, source synchronization used:

```sh
git ls-files crates programs Cargo.toml Cargo.lock > /tmp/cx-devnet3-source-files.txt
rsync -a --files-from=/tmp/cx-devnet3-source-files.txt ./ \
  dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020/src/
scp scripts/r1_devnet_build.sh scripts/r1_devnet_receipt.sh \
  scripts/r1_devnet_release_gate.py config/r1-devnet.template.json \
  dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020/
```

On the host, expected time is incremental compilation, not proving:

```sh
cd /home/dombarker/project-offloads/codex-cx-devnet-20261020
systemd-run --user --scope --unit=cx-devnet3-build \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash ./r1_devnet_build.sh "$PWD" devnet fa894d83d frozen
```

This uses `pool-adapter,private-leaf-salts`, SBF 3.1.13/platform-tools v1.52,
`--offline --locked -j 4`, and the retained task SBF cache. It reads the
reserved Pool/registry IDs from the JSON config. Native commands retain
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`; SBF removes that cc-driver spelling
and passes `-C link-arg=--threads=4` directly to rust-lld.
The optional fourth build argument names a receipt/artifact series so old
attempts remain intact. This run produced `artifacts/frozen-devnet/` and
`receipts/build-frozen-devnet/`.

## Config-driven release gate

On the host, expected time is byte comparison and read-only RPC:

```sh
cd /home/dombarker/project-offloads/codex-cx-devnet-20261020
systemctl --user list-units --type=scope --state=running --no-pager \
  > receipts/resume-reservations.txt
systemd-run --user --scope --unit=cx-devnet3-preflight \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash r1_devnet_receipt.sh receipts/resume-preflight-run fa894d83d \
  'Read-only ELF byte audit and finalized RPC reads; no proving or submission' \
  python3 r1_devnet_release_gate.py r1-devnet.template.json receipts/resume-preflight
```

Executed exit: **4**, solely because `declared_default_elf_sha256` names
`f11e40b4…`, the LLBC hash. Documented default ELF `dfc2a91a…`, rebuilt devnet
ELF `fb2fc048…`, Pool and registry all match their inventory pins; section
layouts, `.text`, both IDs and the exact two-slot patch pass. Genesis, TxV1
activation and permanent rent coverage also pass. Each RPC request/response
and attempt timing is retained. Read-only transient RPC errors have bounded
retries; no signing, transaction submission or key access exists in this tool.

The config deliberately retains the disputed declared hash. After a lead
correction, update that field and use new receipt directories for a new gate.
Exit 0 would mean these listed preflight checks pass; it would not establish
working uploads, proof acceptance or settlement.

## Work still required

There is **no end-to-end RPC spend driver** in this result. The raw-buffer
carrier, real setup/deposit, retrying live-state proofs, 3,763-byte uploads,
checkpoint creation, tx1/tx2 confirmation/expiry handling, state readbacks,
negative checks and phase measurements remain open after release admission.
Do not use legacy verifier tags 4/5/6: the frozen entrypoint rejects them.

[Prior commands](README-prior-cx-devnet2.md) and
[prior report](REPORT-prior-cx-devnet2.md) describe superseded artifacts only.
