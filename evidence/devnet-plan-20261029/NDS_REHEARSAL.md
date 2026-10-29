# NDS rehearsal — NOT RUN (mandatory wiring stop)

No validator was started; no accounts cloned; no ELF deployed locally; no keys
created; no registry/Pool writes, proof generation, TX1 or TX2 attempted.
There is no successful rehearsal receipt or local loaded-ELF hash claim.

The stage-1 stop gate was reached before stage 2: the existing Pool's registry
is immutable and rejects new entries. Cloning that state faithfully preserves
the blocker. Editing its bytes or resetting its authority would not rehearse a
permitted devnet operation. A fresh mint/Pool demo would test a different state
scope and requires lead/owner disposition before proceeding.

Receipts actually produced:

- NDS_RPC.json: exact unsigned RPC requests and responses, UTC timestamps;
  getVersion ×1, getBalance ×1, getMinimumBalanceForRentExemption ×3,
  getAccountInfo ×3. No transaction/simulation/signature RPCs.
- NDS_STATE.json: decoded registry flags/zero authority, entry, Pool state.
- NDS_KEYS_PUBLIC.txt: SSH metadata checks failed because documented paths
  were absent. No private bytes or fresh public-key derivations were obtained.
- NDS_SOURCE_PINS.json: source revision and hashes of inspected code/config.
- NDS_ATTEMPTS.jsonl: commands, outcomes and explicit stop; no omitted failed
  deployment or spend attempts.

Capture command: `python3 evidence/devnet-plan-20261029/NDS_readonly.py` (exit 0).
The capture refuses to overwrite its receipts. Do not rerun it in this directory.
The SSH command is recorded verbatim in NDS_ATTEMPTS.jsonl; exit 1.

Validation is receipt decoding and source inspection only; prior NCY ELF
reproduction and NDQ chain hashes are reused, not rerun or promoted into a
local integration result. No Lean, Rust, Kani or full manifest replay ran.
