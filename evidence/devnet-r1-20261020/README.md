# R1 devnet resumption evidence

**Blocked before deployment.** See [REPORT.md](REPORT.md). This directory has
no R1 landing signatures, spend timings, CU observations or completed demo.
The complete spend driver requested in stage 5 is still open.

Two independent blockers: the fresh devnet payer's airdrops returned a rate
limit and its balance is zero; the pinned verifier authenticates hardcoded
audit Pool/registry IDs instead of the fresh deployment IDs. The legacy
verifier upload lifecycle is also excluded by its pinned entrypoint guard.
Do not deploy incompatible programs just to get deployment signatures.

The public [config template](../../config/r1-devnet.template.json) contains
the retained task's reserved program IDs, a null mint, and host-local ELF
paths. It contains no keys. Update public addresses and paths for another
task. Preserve all existing keys in the host's task `keys/` directory.

Run the read-only preflight from this worktree:

```sh
bash -n scripts/r1_devnet_preflight.sh
scp scripts/r1_devnet_preflight.sh config/r1-devnet.template.json \
  dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020/
ssh dombarker@100.108.41.90
cd /home/dombarker/project-offloads/codex-cx-devnet-20261020
/usr/bin/time -v -o receipts/preflight-next.time \
  bash r1_devnet_preflight.sh r1-devnet.template.json receipts/preflight-next \
  >receipts/preflight-next.stdout 2>receipts/preflight-next.stderr
```

Use a new receipt name on each run. The script does not sign or mutate
accounts. It records finalized genesis, node version, slot, TxV1 feature,
the payer/program/audit accounts, and hashes of the three local ELF files.
It deliberately exits 4 after collecting observations: it cannot certify a
working spend driver. Transport/JSON-RPC failures stop earlier with raw error
receipts; a non-devnet genesis stops before account queries.

Original funding attempts, made in the retained host task directory:

```sh
export PATH="$HOME/.local/share/solana/install/active_release/bin:$PATH"
solana --url https://api.devnet.solana.com airdrop 5 --keypair keys/payer.json
curl --fail-with-body --silent --show-error --max-time 45 \
  -H 'content-type: application/json' \
  --data '{"jsonrpc":"2.0","id":1,"method":"requestAirdrop","params":["Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD",1000000000,{"commitment":"finalized"}]}' \
  https://api.devnet.solana.com
```

These failed requests are evidence, not a funding loop. No alternate wallet
or funds were used. No transaction signature exists for either request.

Before implementing the spend driver, resolve deployment identity compatibility
and choose a supported proof/statement carrier. Any source changes to the
verifier require new ELF pins and focused Rust validation; they cannot preserve
the currently mandated verifier hash. The current host artifacts are reusable
for inspection without rebuilding them.

Future heavy Rust/SBF/proving jobs must run on the host, with an optimized
profile, `-j 4`, and `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`, inside their
own `systemd-run --user --scope` with `MemoryHigh=6G`, `MemoryMax=8G`,
`MemorySwapMax=0`, `TasksMax=64`. Check the aggregate populated reservation
before launch (55 GiB working limit). Record command, source revision, exit,
wall time, peak RSS and swaps. No such build was needed for this blocked run.
