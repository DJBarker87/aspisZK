# Positive-transfer COMPLETE integration

Local gate and repaired devnet transfer passed. The finalized atomic transfer used
1,105,880 CU of the declared 1,200,000. See [the live report](live-demo-report.md)
for signatures, settlement assertions, controls, costs and artifact provenance.
This is experimental engineering evidence. Full-view ZK, Fiat–Shamir and global
accepted-proof recovery remain open. No production activation is claimed.

Research base: `e90e7338656f221c9a1bbde90d533ba94d002014`.
Deployment infrastructure: `6a32de2656002fb9ab6160f37c4a9b3d9bc993a8`.
Own branch/worktree: `research/v8-positive-complete-devnet-20260909` /
`/Users/dominic/ZK/.worktrees/ZK-v8-positive-complete-devnet-20260909`.
Main and the actively edited research worktrees are untouched.

The opted-in repair adds the reviewed lane94 inverse-product residual requiring
both transfer output amounts to be nonzero. The 107-byte descriptor retains the reviewed mask inventories, layout and
active-cell overwrite rule, and explicitly binds the prior COMPLETE profile as
parent. That parent differs from the standalone opt-in host run’s V7 default
profile; it is a recorded transcript-input change, not byte-identical framing.
The SBF path uses exact frozen descriptor bytes; the host checks equality with
the original enumeration and 32 arbitrary-QM31 packing controls. No existing
semantic, canonical, carried-image, shifted-row or shifted-query check is removed.

New outer profile/release hashes in `profile.json` separate this semantics from
the earlier COMPLETE profile. The compiler checks the original authoritative
transition before adapting a zero-output control; each adapted statement is
re-encoded and its account-bound attempt digest recomputed before C1 commitment.
Only transfer is supported. Withdrawal is rejected by this profile.

The unchanged isolated Pool and Registry programs from the preceding demo are
reused with a fresh mint, master, lane/history/checkpoint/registry-entry state
and fresh verifier/proof identities. Neither existing program is upgraded.
The first unused Pool identity and its key are retained; switching to the
unchanged deployed Pool saves 2.733370200 SOL of duplicate rent. Local proofs
and measurements for both public identity configurations are preserved.

Final local configuration: real COMPLETE transaction 1,150,565 CU, declared
1,200,000, TxV1, 845 wire bytes, 256 KiB heap. Recipient-zero and change-zero
controls reject semantic error4 at 519,470 and 519,472 CU, with byte-exact rollback.
These negative bodies contain actual C1/C2 commitments and ten semantic rounds;
the later PCS suffix is deliberately unconstructed. They establish rejection at
that semantic boundary, not a full accepting adversarial proof or universal theorem.
`evidence/local-gate.json` pins the tested verifier hash. `deploy.py` requires it.

The first SBF compile failed because host-only mask helpers were included;
correct cfg separation fixed it. The first local transaction exposed the old
harness's 1.4M diagnostic default overriding its requested heap; selecting the
real 1.2M transaction configuration fixed it. Both failures are retained.
A later rerun refused to overwrite old Registry sidecars; those were archived
before retrying. No failure was discarded or counted as success.

## Reproduction

Builds use the task-owned NUC copy
`/home/dombarker/project-offloads/aspis-v8-positive-complete-20260909`.
It was copied with independent files/cached dependencies from the preceding
pinned build archive, then overlaid with the seven committed source files in
`upstream/` and `prepare_integration.py`. That adapter records every modified
input hash in `integration-inputs.json`; `check_inputs.py` checks them. It does
not run in a git worktree or change production/default sources.

All large jobs use optimized cached/offline builds with 2 build jobs and
systemd scopes MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0. Existing wrapper
`run_complete_build_nuc.sh` runs the selected terminal-stack SBF, partial-host
prover and matched driver builds with the additional explicit positivity cfg.
The source hash checker is replaced only for the intentionally changed input
set by `check_inputs.py`; the archived original checker is not misrepresented
as authenticating new source. Build failures and /usr/bin/time resource logs
are retained under `evidence/`.

`run_local_nuc.sh context`, then `prove CASE`, then `run CASE` executes the
local gate for honest, recipient_zero and change_zero. Local setup is clearly
synthetic LiteSVM fixture injection; devnet setup uses actual supported
loader/System/SPL/Pool/Registry/proof-lifecycle instructions.

The devnet order is: `devnet.py gate`; authenticate unchanged Pool/Registry;
upload/deploy/authenticate the new verifier; `devnet.py setup`; run the release
tools' `validate-setup` against the finalized snapshot; `lifecycle_preflight.py`;
`certify_verifier.py`; `devnet.py registry`. Only then export `tools context`
from `authoritative-before-proof.json` into a fresh private `positive-live-context`
on the NUC and execute `run_live_prover_nuc.sh`.

Copy the resulting honest context/proof and recipient_zero/change_zero artifacts
to the corresponding retained private local directories. Run
`zero_output_controls.py` before `run_transfer.py` (which additionally checks
noncanonical proof rejection, genuine settlement and replay). Upload/setup
transactions are counted separately from the atomic settlement. The verifier's
required immutability is applied only after local and live setup/lifecycle gates;
its loader rent then becomes irrecoverable. Pool authority remains retained.

The user authorized existing devnet funds and a cumulative 25-SOL budget. This
run received 6 SOL from the dedicated Colosseum regime test wallet, bringing
cumulative external funding to 24 SOL. Its donor retained 1.896892640 SOL.
Keys stay local; no program/game accounts in other repositories were closed.
