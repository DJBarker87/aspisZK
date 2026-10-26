# Operational proof-account client receipts

Source boundary: baseline/head before implementation `149855299b`; parked
candidate read via git objects `1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8`.
Production wiring is `b7cd400a55`; corrected route test is `5270ce4bf3`.
Final integration harness source is `ce5583a4a2`; the runner/prover source bytes
are unchanged between the successful build-03 and runtime-02. Exact commands,
full revisions and input SHA dictionaries are in each `*-config.json`,
`*-inputs.json` and `*/receipt.json`.

`runtime-02-public/acceptance.json` is the acceptance receipt: actual
`devnet_spend` subprocess proofs, OS entropy, real retained ledger, signed
LiteSVM stage1/stage2 and actual planner Pool settlement. Transfer and withdrawal
both pass with default verifier `f8c0ec72…`, devnet verifier `63ad3e9c…` and Pool
`121f3e29…`. Four proofs succeeded on attempt 1. Every selected key occurs in
its durable record. Each reopened-ledger selected-adapter duplicate returns
`Semantic`, even under a second valid statement, leaving all records unchanged.
The three runner unit tests additionally exercise duplicate keys in the input
ABI and synthetic first/retry/eighth successful account selection.

The command in runtime-02's receipt is:

```
native-target/release/pv_client_gate \
  /home/dombarker/project-offloads/codex-pv-client-20261026/native-target/release/devnet_spend \
  artifacts/default.so artifacts/devnet.so artifacts/pool.so \
  /home/dombarker/project-offloads/codex-pv-client-20261026/runtime-02-private
```

The actual argv uses an absolute gate path too; see the receipt. SHA/size pins
for both binaries, three exact loaded ELFs, unchanged admission/receipt scripts,
compiler, CPU, flags and features are in `runtime-bundle.json`. The ELF copies
come from s10-repin3's **artifacts/*.so**, not its different unstripped linked.elf.
Each runtime `loaded-*.json` verifies immutable Program/ProgramData loader
metadata and exact executable bytes. No SBF rebuild or artifact substitution.

## Measured host runs

All scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Cargo:
release/opt-level=3, locked/offline, four jobs. One scope at a time. Every
receipt records exact source revision, input dictionary fingerprint, status,
wall time, process/child peak RSS, cgroup peak and swap. `#print axioms` is N/A
for all Rust/Python/native runtime runs; no Lean theorem was added.

| Target | Exit | Wall s | Peak RSS KiB | Swaps | Source revision |
|---|---:|---:|---:|---:|---|
| unit-01 | 101 | 34.515 | 563488 | 0 | b7cd400a55 |
| unit-02 | 0 | 0.617 | 225772 | 0 | b7cd400a55 + pinned test correction |
| build-01 | 101 | 1.113 | 248892 | 0 | 7c63aed20f |
| build-02 | 0 | 1.507 | 342992 | 0 | 6a1a7ce414 |
| runtime-01 | 1 | 42.843 | 538296 | 0 | 6a1a7ce414 |
| build-03 | 0 | 1.632 | 346908 | 0 | ce5583a4a2 |
| runtime-02 | 0 | 195.957 | 547352 | 0 | ce5583a4a2 |

Failures are retained, not replaced by successes: unit-01's new lexical guard
matched `prover::` inside `aspis_prover::`; unit-02 corrects the token check.
Build-01 lacked three fixture-helper imports (and consequent type inference);
build-02 fixes them. Runtime-01 accepted default transfer stage1/stage2/Pool,
then rejected devnet stage2 because that ELF embeds different Pool/Registry
IDs. Runtime-02 changes the fixture construction to bind each mode's actual
IDs, producing separate proofs. No failed command was rerun with unchanged
inputs or raised caps. Unit-02's generic `expected_time` label accidentally
mentions proof generation; its actual command/output is only the three tiny
unit tests. The script now labels all unit-* commands correctly.

The first unit-02 preflight was refused at 51,942,260,736 reserved bytes plus
8 GiB against the 55 GiB safe limit; no scope ran. Its original inventory is
`unit-02-reservation-refused.json` (09:26:43 UTC). Retry admission is
`unit-02-reservation.json` after the required three-minute wait. No barrier
bypass, cap increase or host infrastructure repair was performed.

## Limits and retention

Raw proof/public carriers and authenticated registry/master/checkpoint/lane
images are preloaded fixtures. Stage1, verifier stage2 and Pool terminal execute
the real pinned ELFs; the actual runner's settlement validator checks the
resulting lane root/frontier/index and consumed nullifier. These are fixture
acceptance measurements, not live RPC deployment, registry provisioning,
carrier creation/upload, account-reachable-state certification, privacy,
constant-time, or whole-prover equivalence proofs. The registry executable
hash descriptors are fixture values, explicitly not an attestation of registry
provisioning (`loaded-*.json` also records this distinction).

All task keys (mode 0600), recovery files and nonce ledgers remain on the host
under the two `runtime-*-private` directories in `runtime-bundle.json`. Only
public JSON requests/plans/transaction hashes/logs and loader hash receipts are
exported. No key, proof binary, ELF, object or archive is committed. There was
no network funding, refund or key destruction; no refund destination or
signatures exist. LiteSVM's synthetic balances do not fund network accounts.
No production wallet or other worker's key directory was accessed.

31 small local Python lifecycle/inventory tests passed (`lifecycle-tests.log`);
RSS/swap were not measured for that non-release local test. Retained historical
`source-audit.json` and `PV_Client_audit.py` describe the old baseline mismatch:
the latter intentionally refuses the now-changed operational source. Use
`PV_client_pins.py --check` for the new source dictionary and entry chain.

No Lean/Kani budget is spent on an unchanged theorem: this job removes the
operational source mismatch and supplies runtime integration subgate evidence.
`RustRealRefinement`, E1/E2, RunJoin, native L1/L2/L3/Drop/error transport,
fixed-coin 1000 comparisons, performance/adoption and coherent final release
replay/axioms obligations remain. No privacy endpoint is claimed proved.
