# Isolated V8 COMPLETE devnet demonstration

**Status: genuine positive COMPLETE transfer finalized on devnet at 1,083,081 CU / 1,200,000 declared. Exact settlement checks passed; malformed and replay controls rejected unchanged.**

See [live-demo-report.md](live-demo-report.md) for signatures, final metrics, account transitions and funding.

See [checkpoint-fix-review.md](checkpoint-fix-review.md) for the cause, explicit setup extension and measured controls.

Experimental engineering test in progress. No production activation or claim
that soundness is complete. Global recovery, payment/source refinement,
Fiat–Shamir and full-view ZK remain under formalisation.

Base commit: `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee` from the committed
`research/v8-no-work-100-20260907` branch. The source research worktree had
active uncommitted formalisation work and was left untouched. This work uses
`research/v8-isolated-devnet-smoke-20260909` in the isolated worktree
`.worktrees/ZK-v8-isolated-devnet-smoke-20260909`.

## Provenance and deliberate changes

The original selected terminal-stack COMPLETE verifier was checked directly
against its archived NUC artifact: 1,027,608 bytes, SHA256
`3d07a23833bac533f791b7ce2d619f4cd40aff6e1b5314c3b43be596b38c15a3`.
The recorded terminal-query ledger audit passed: 122 complete cases and
15 clean axiom audits. This is an audit of existing evidence, not a new formal replay.

That ELF dispatched only ASQ8 verification. It could not initialize, upload,
seal or close a proof through legitimate transactions. Its capability also
pinned the local fixture Pool and Registry identities. The scoped build
adapter substitutes the new public identities and routes lifecycle tags
0, 1, 62 and 64 to the existing authenticated handlers. ASQ8 still calls
the selected COMPLETE verifier with its checks intact.

The resulting verifier is 941,672 bytes with SHA256
`f4527ee759b66aeb21dc3b23bdc7a081e9e4f0b377dc32856873593ce8828e42`.
It is **not byte-identical** to the archived ELF. `build-inputs.json`,
`identities-at-build.json`, `prepare_build.py`, `verifier_entry.rs` and
`proof_lifecycle.rs` record the changed inputs. `prepare_nuc.sh` records the
preceding frozen patch chain and source checks. The initial deployed Pool and Registry retained the archived hashes. The later
checkpoint fix adds a default-off Pool setup extension and requires a new Pool
and rebound verifier. Current hashes are in `elf-hashes.json`; initial hashes
are retained in `pre-checkpoint-fix-elf-hashes.json`. The existing isolated
Registry image is reused, with a fresh registry account for the new master.

The compiler/prover keeps QM31, q22, the current domain, canonical fields,
the 40,282-byte body ceiling, the carried image gate, shifted ordinary rows
and shifted query batch. The host input adapter reads the authoritative live
statement and membership before proof generation. It uses exactly seed 1 and
rejects the maximum-frontier scan environment variable. No favourable
transcript search or grinding security credit is used.

## Live setup replacing injected local fixtures

The benchmark injected program images/ProgramData, funded accounts, master,
checkpoint, lane, history and already-sealed proof accounts. Token controls
also injected mint/vault state. This demo uses the native loader, System
Program, SPL Token and authenticated Registry/Pool/proof lifecycle instructions.
The eight-lane checkpoint repair adds explicit AS8V preparation and AS8K
finalization instructions, preserving every root check and the atomic transfer.

The fixed synthetic input note is 1,000 token base units. Its transfer creates
recipient and change notes of 600 and 400. Both output owner keys are derived
from retained fixed synthetic secrets, so the outputs have known spending witnesses. Thirteen notes from the fixed
deposit sequence provision the selected output lane's current history page.
This is ordinary account provisioning before a proof/transcript exists.
The input is deposit zero. `plan.json` contains the supported instruction
metas and public account addresses. No original pool, mint or witness is reused.

The Pool's terminal instruction leaves the proof sealed and read-only.
Consumption is enforced by the nullifier marker. A malformed proof control
uses the same proof-account identity as the positive proof, changes only the
first body field to the noncanonical modulus, and uses the existing close/refund
and recreate lifecycle before uploading the genuine proof. Replay rejection
is checked with fresh transaction blockhashes.

## Runtime and funding

The public endpoint and Helius devnet endpoint both returned devnet genesis
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG` and runtime
`4.3.0-beta.3` (feature set `2409014235`). The TxV1 feature account
`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` is activated at slot
492480000. Signed TxV1 simulation passed with explicit 1,200,000 CU,
10,000 lamports priority fee, 8 MiB loaded data and 256 KiB heap.
RPC evidence is retained under `evidence/`. Later Helius response contexts also
reported `4.3.0-alpha.2`; load-balanced response versions are preserved per call.
The successful resumed live run repeated the genesis/feature/signed-TxV1 gate.

The user authorized up to 25 faucet-funded devnet SOL and funded the fresh
payer with 10 SOL. The first deployed programs retain 8,435,741,320 lamports of rent.
The new Pool/verifier require another 7,518,775,920 lamports. Under the user’s
explicit recovery authorization, two dedicated Colosseum devnet test wallets
provided 8 SOL, bringing total external funding to 18 SOL within the 25-SOL
budget. They retained 0.998280480 and 1 SOL respectively. The funding transaction
is `4hnKG3nVMZdttprgSEZqAmEhGajvaNPpPRL9BuaCmWtn6FDPwrLudBDNActQb7L8JYEV9snUoE8jKno9Tb12Ukn5`.
See public receipts in `evidence/live-checkpoint-fix/`. No accounts or programs
from the other repositories were closed.

The new Pool retains the experiment payer as upgrade/close authority. The
verifier is initially deployed with that authority too. Only after live setup
and init/upload/seal/close lifecycle gates pass does `certify_verifier.py`
remove the verifier authority: the existing Registry V2 requires an immutable
verifier. That step makes verifier rent irrecoverable; it does not remove Pool
authority. This differs from the frozen benchmark’s immutable fixture Pool.
All task keypairs, including loader buffers, are retained outside the repo
under `~/.local/share/aspis/v8-devnet-smoke-20260909/keys`, with private file
permissions. No keys or secret-bearing logs may be committed. No cleanup
deletes keys; refunds must be finalized and checked before any separately
authorized key deletion.

The existing Helius API key is read from private configuration, used only
with a fixed devnet host, and redacted from logs. Production wallet material
and existing deployment defaults are not read or changed.

## Commands

Local tools: Solana CLI 2.3.0, Python 3.12 and solders 0.27.1. Heavy builds
use `dombarker@nuc.local`, cached dependencies and the explicit cgroup caps
in `prepare_nuc.sh`. SBF platform tools are v1.54 (Rust 1.89 development
toolchain); host Rust is 1.94.1. Build logs include flags, exit statuses,
wall time, maximum RSS and swap. No paid build jobs are used.

From the isolated worktree:

```sh
export ASPIS_RPC_PROVIDER=helius
python3 docs/research/v8-isolated-devnet-smoke-20260909/devnet.py gate
python3 docs/research/v8-isolated-devnet-smoke-20260909/upload_program.py verifier
python3 docs/research/v8-isolated-devnet-smoke-20260909/deploy.py verifier
# Repeat upload_program.py and deploy.py for the new pool.
# Registry is already deployed in this isolated experiment: authenticate it; do not redeploy.
python3 docs/research/v8-isolated-devnet-smoke-20260909/authenticate_programs.py
python3 docs/research/v8-isolated-devnet-smoke-20260909/devnet.py setup
# Run tools validate-setup on initialized-state.json and save validated-live-setup.json.
python3 docs/research/v8-isolated-devnet-smoke-20260909/lifecycle_preflight.py
python3 docs/research/v8-isolated-devnet-smoke-20260909/certify_verifier.py
# Generate registry-plan.json using tools registry and a current finalized slot.
python3 docs/research/v8-isolated-devnet-smoke-20260909/devnet.py registry
# Export context with tools context from authoritative-before-proof.json.
# Generate the proof on the NUC only after that context exists (commands below
# are recorded in run_live_prover_nuc.sh and evidence/live-prover.log).
python3 docs/research/v8-isolated-devnet-smoke-20260909/run_transfer.py
```

The initial CLI uploads exhausted bounded retries, first through the public
RPC and then Helius. Their buffers were retained and reused. A 2,800-byte
native-loader write failed simulation with InvalidInstructionData; the
native loader retains a 1,232-byte instruction deserialization limit.
The replacement uses three supported 1,200-byte loader writes per TxV1
setup transaction. These setup uploads are separate from atomic settlement.
Failure logs and exact simulation evidence are preserved.

The Pool upload also exposed unlanded RPC submissions. Eight initial batches
expired without appearing in finalized signature or transaction lookup; one
replacement also expired. These receipts are preserved as `expired.json`.
The uploader checks authoritative missing ranges, proves an old attempt's
expiry before re-signing, simulates each new signed transaction, and supports
bounded rebroadcast of identical signed bytes. It does not alter proof seeds,
verification, compute limits or the settlement protocol to recover transport.

## Resume without replacing keys

Current identities and private filename mappings are in `identities.json`.
The original and two-note experiment configurations are archived separately.
Do not rerun key generation, overwrite existing keys or upgrade an existing
program. `deploy.py` refuses an existing on-chain program and resolves the
explicit retained key mappings. All local key files remain private.

With funding restored, run the commands above for the fresh
verifier and Pool, authenticate all three program images, then run setup.
Setup uses thirteen deposits, eight strict lane validations, and one atomic
checkpoint. Upload/setup fees are separate from atomic transfer fees.

Generate a registry plan with the release tool (the supplied slot is replaced
by a fresh, durably recorded scheduling slot after initialization):

```sh
# In the task-owned NUC archive, after syncing identities.json and elf-hashes.json:
demo-host-target/release/aspis-v8-devnet-tools registry \
  docs/research/v8-isolated-devnet-smoke-20260909/identities.json \
  docs/research/v8-isolated-devnet-smoke-20260909/elf-hashes.json 1 \
  > docs/research/v8-isolated-devnet-smoke-20260909/registry-plan.json
```

Copy that public plan locally and run `devnet.py registry`. It uses nonzero
minimum delay, schedules against a fresh slot, waits for that slot, then
activates and freezes. The old zero-delay failure remains recorded. Never
reuse the old registry entry or proof context for the new program identities.

Copy `evidence/live-checkpoint-fix/authoritative-before-proof.json` to the
task-owned NUC archive. Generate context there with the optimized tools:

```sh
demo-host-target/release/aspis-v8-devnet-tools context \
  docs/research/v8-isolated-devnet-smoke-20260909/identities.json \
  docs/research/v8-isolated-devnet-smoke-20260909/evidence/live-checkpoint-fix/authoritative-before-proof.json \
  /home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909/live-context
```

The output directory must not exist. Protect it with `umask 077`. Copy context
to the retained local private `context` directory. Proof generation, only
**after** that live context is verified, uses both context environment variables:

```sh
systemd-run --user --scope --unit=aspis-v8-live-prover \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 \
  ASPIS_V8_LIVE_CONTEXT=/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909/live-context \
  ASPIS_V8_COMPLETE_CONTEXT=/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909/live-context \
  docs/research/v8-no-work-100-20260907/experiments/performance-host/target/release/aspis-v8-performance-host \
  /home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909/live-proof
```

This is an optimized proof-generation job, not a compilation job. Inspect
host reservations first; keep aggregate caps within the safe host limit.
Copy the proof to the retained private `proof` directory, preserve prover
resource/timing logs after checking they contain no secrets, then execute
`run_transfer.py`. Its exact positive and negative transitions passed; see live-demo-report.md.

For the executed checkpoint regression, `run_checkpoint_nuc.sh` records
bounded cached build and replay commands. `prepare_checkpoint_receipts.py`
generates the setup extension from the frozen checkpoint planner and processor;
`checkpoint_receipts_generated.rs` is the actual compiled source. The scalar
hash experiment is retained as an unsuccessful alternative, not a build input
for the selected fix. No package-wide formal replay was run.
