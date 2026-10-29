# NDZ local rehearsal procedure and evidence boundaries

All public-cluster access in this task is read-only RPC. No public-cluster
transaction, airdrop, signed simulation, or signature was sent. The new devnet
verifier key exists locally only. No crates/programs changed; no release ELF
was patched or rebuilt. No push was performed.

## Identity and dependencies

NDZ_STAGE0.md and NDZ_ELF_SCAN.json establish the fresh-address gate using
frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, a freshly hashed release
ELF, and freshly downloaded deployed dependencies. All crates/programs at the
inspection revision dfa35acd8390aea176c13710d320d041332b320a are identical to the
frozen revision. The native selected64 client is built from the inspection
revision; its tools sources include the approved bounded account-selection route.

Public dependency downloads used only `solana program dump --url devnet`:
Pool BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs,
registry 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q,
carrier 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN.
Their exact hashes/lengths are in NDZ_ELF_SCAN.json.

## Host and resource controls

Host root: `/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029`.
The task source and copied incremental cache are private to this root. Four
native-client preflights repaired missing archived path-dependency/include
files; no source code was changed. The successful command is recorded in
NDZ_client-build4.time/log: optimized `cargo build --release --locked --offline
-j 4 --features r1p-check --bin devnet_spend`, target/cache NDZ_native-target,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0. Expected work was compilation/linking,
not proof generation. The exact successful wall/RSS/swap/exit are retained.

The official Agave v4.2.0 runtime was restored using the repository's pinned
runtime acquisition script. solana SHA256 is
b6134ccddcb3456e49c0c15bc028c2902184a8fef6f6e6e665d9f8ae5bea8d10;
validator SHA256 is
78ee817e9a4fade8a6606ee663060d39728017c79ebac7a7cd35b2a985066f6a.
The archive was checked against the repository's release/tag/commit and hash
pins. Runtime download/extraction used a 1 GiB, zero-swap scope.

Validator service: MemoryHigh=3G, MemoryMax=4G, MemorySwapMax=0, TasksMax=512,
CPU affinity 0–3. An initial TasksMax=256 start failed to spawn enough threads;
it was corrected without increasing memory. Keys/ledgers were retained.
NDZ_start_validator.sh binds to 127.0.0.1:18995 (final ledger; earlier ledger used port 18993) and clones the three real-ID
programs and devnet feature set. Only the cloning operation contacts devnet,
using read-only RPC. Every signing/write endpoint is the literal loopback URL.

The first default-feature validator was used for an intentional post-buffer
signer failure. Its buffer was fully refunded to the retained local payer,
then reused for an ordinary deployment attempt. The latter was interrupted
with SIGINT after identifying the rent/feature mismatch; it also refunded the
buffer and ended with an empty inventory. This old ledger and all its keys
remain retained. It is not the successful release rehearsal ledger.

The final evidence ledger uses `--clone-feature-set` and `--limit-ledger-size 1000000`. The runtime still ages old signature-index entries; the complete final set therefore relies on immediate finalized metadata capture, checked against every currently indexed signature plus exact lamport conservation (NDZ_COLLECTION_AUDIT.json). The first full spend run succeeded, but its default history retention pruned CLI deployment/finalization metadata before collection. That run is diagnostic/proof-generation evidence only; it is not the complete transaction evidence release. Immediate CLI metadata capture and history retention were corrected, and the final deployment/spend replay is justified by that specifically missing evidence artifact (AGENTS.md cadence rule 5). No unchanged formal manifest was rerun. The final ledger repeats normal initialization with the same retained local identities, and reuses the successfully generated proof artifacts through the repository client’s validated resume path; NDZ_PROOF_REUSE.json records their hashes, identities, selection attempts and original generation times. Fresh TX1/TX2 signatures and finalized metadata are still required on this ledger. The final ledger is retained alongside all earlier ledgers.

The fresh ledger uses `--clone-feature-set`. This corrects the
runtime's feature-gated deployment rules, including leaving the future ban on
SBPF v0/v1/v2 deployment inactive. Agave 4.2 test-validator nevertheless retains
genesis rent of 6,960 lamports per byte; current devnet quotes 5,080. Its rent
transition is applied on new feature activation, not reconstructed merely by
cloning active flags at genesis. See [Agave’s activation logic](https://github.com/anza-xyz/agave/blob/v4.2.0/runtime/src/bank.rs#L5676-L5722). The local rent result is therefore a higher
cost stress test, not a claim of exact devnet runtime equivalence. Devnet at
inspection reports 4.4.0-beta.1; local reports 4.2.0. These differences remain
part of the real-devnet execution obligation.

## Successful route

NDZ_prepare_local.py verifies the cloned ProgramData payloads against their
exact pinned ELF extent (allocation suffix must be zero), registry immutability,
TxV1 activation, and a local genesis payer balance of exactly 18.35320408 SOL.
The payer/verifier/buffer keys are generated only under the evidence keys/
root. No public payer secret is used on the host.

NDZ_run.py records exact commands, code hashes, wall time, cgroup peak/swap,
exit and GNU-time RSS. Deployment uses the repository paced loader-v3 path,
900-byte chunks, simulation before each submission, finalized signatures,
full buffer byte comparison, --max-len 1563728, exact ProgramData payload
comparison, then set-upgrade-authority --final. The final buffer list is empty. The loader [drains buffer funds before ProgramData allocation](https://github.com/anza-xyz/agave/blob/v4.2.0/programs/bpf_loader/src/lib.rs#L267-L288); the conservative funding bound nevertheless reserves both.
NDZ_VERIFY_PUBLIC.py independently checks loader owners/tags, linked ProgramData,
revoked upgrade authority, exact payload extent and SHA256 at finalized commitment.

The configuration changes the payer/keys, endpoint/genesis and verifier ID,
adds a fresh key namespace, and sets pool_initialize_after_registry=true.
The spend driver creates a fresh mint and token accounts, initializes the new
registry for the future Pool PDA, schedules/activates/freezes the release entry,
then initializes the fresh Pool. It deposits both fixture notes, checkpoints,
and runs transfer and withdrawal TX1/TX2, replay rejection, mutated-proof
rejection and proof restoration through the repository script. The unchanged
programs permit this ordering. No old Pool state is read for initialization,
rewired, migrated or reused for the spends.

NDZ_collect.py reads finalized local metadata for every payer signature and
records fees, CU, payer balances, all newly funded accounts (including CPI
PDAs), final rent and live devnet quotes. NDZ_ASSOCIATE.py checks the fresh
Pool policy, immutable registry, active exact profile/release entry and linked
immutable release ELF in one finalized account snapshot. Its local result is
not a public-chain association.

Legacy raw driver receipts include hard-coded devnet Explorer links even for
loopback transactions. Those links are not chain evidence. Published transaction
rows identify only local signatures and the loopback RPC; the source now omits
Explorer links for loopback URLs. Raw host receipts remain unchanged, with their
actual source hashes recorded. Later receipt/cleanup checks strengthen the
same transaction path; they do not change program or proof instructions.

## Writer preparation and retention

NDZ_WRITER_READINESS.json records the exact client/CLI binary hashes and the
Mac Docker image ID. The Linux amd64 client ran a public-only setup plan under
emulation with network disabled, MemoryMax=4G and swap cap 0. No keys were in
the image or mounted for that check. Separate keygen pubkey calls through the
writer launcher checked both retained public identities in place; they generated
no signature. NDZ_writer.sh mounts the payer file read-only, the durable task
key directory read-write, and only the reviewed receipt subdirectory writeable
inside the worktree. The runbook uses these same binaries without a new native
Mac or release-ELF build.

The fresh verifier key is retained outside build/offload directories. No secret
was printed, copied, hashed or committed; no key was destroyed. Backup status
is not asserted by this worker, which was prohibited from copying secrets.
The lead must retain the authority directory and satisfy the policy's backup
requirement before the separately reviewed public run. There is no cleanup
command for task keys. See NDZ_KEY_RETENTION.md and NDZ_LOCAL_KEYS_PUBLIC.json.

An additional writer compatibility check generated one fresh selected64 proof in
the exact Mac writer image, with eight fresh local nonce-account keys, no devnet
key mounts and networking disabled. It exited zero in 39.335 seconds (one attempt),
cgroup memory peak 618475520 bytes, swap peak zero, under the same 4 GiB zero-swap
cap. Private keys/nonce state remain under the Mac evidence keys/ directory; only
public input/result metadata was published. No signature or transaction was
generated. This is a tooling compatibility check, not a public runtime result.
