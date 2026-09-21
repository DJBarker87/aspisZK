# Refund-recipient privacy cleanup (2026-09-21)

The repository no longer spells out the retired refund wallet identifier.
The configured refund recipient is represented by its role. No replacement
personal wallet was introduced. Transaction signatures, slots, refund amounts,
program identities, proof bytes, SBF bytes and their hashes are preserved.

## Inventory before redaction

The complete reachable-object scan found 36 distinct matching blobs in these
11 paths. Seven paths still contained the identifier on `main`.

| Path | Historical matching blobs | Present on main |
| --- | ---: | :---: |
| `README.md` | 14 | no |
| `docs/reviews/v5-mainnet-deployment-handoff.html` | 2 | yes |
| `docs/reviews/v5-publication-readiness-review.html` | 2 | yes |
| `docs/v5-mainnet-demo.md` | 6 | yes |
| `release/aspis-v5-tag67-mainnet-v1/evidence/mainnet-lifecycle.json` | 1 | yes |
| `release/aspis-v5-tag67-mainnet-v1/manifest.json` | 2 | yes |
| `release/preflight/v5-production-freeze.md` | 2 | yes |
| `release/release-facts.json` | 4 | yes |
| `release/profile23-q18-g37-mainnet-v1/evidence/mainnet-finalized-manifest.json` | 1 | no |
| `release/profile23-q18-g37-mainnet-v1/evidence/mainnet-independent-rpc-reconciliation.json` | 1 | no |
| `release/profile23-q18-g37-mainnet-v1/evidence/mainnet-sweep.raw.json` | 1 | no |

The audit included local branches, tags, stashes, checkpoint trees, GitHub PR
heads, ignored/generated files and linked worktrees. Private executor material
and a local development-context note also contained copies. Private wallet keys
and original executor receipts were retained securely outside the repository.

## Reproduction after the history rewrite

`git filter-repo` replaced the literal and updated dependent SHA-256 checksums
and manifest byte lengths. Historical source identifiers remain in the evidence
as originally published. The [revision map](../release/history-redaction-map.json)
records their cleaned equivalents. The release-facts checker and V5 source
rebuild script resolve these identifiers through
[`tools/resolve_release_revision.py`](../tools/resolve_release_revision.py).
For an older command using a published source ID:

```bash
revision=$(python3 tools/resolve_release_revision.py HISTORICAL_COMMIT_ID)
git show "$revision:path/to/file"
```

Resolve the ID using the current checkout before checking out an old tag.
Source-file and artifact SHA-256 checks remain enforced; mapping a Git revision
does not relax those checks. Rewriting changes commit and annotated-tag IDs;
old commit signatures cannot authenticate the rewritten objects.

The V5 RPC verifier derives the ProgramData-close and payer-sweep destinations
from the archived signed wire, requires them to agree, and compares the
base58-key-plus-newline hash with the previously recorded private pin hash.
It reconciles the proof close, ProgramData close, exact sweep amount and fee,
zero source balances, and the direct refund total without printing the recipient.
The archive's transaction bytes remain available for independent reproduction.
They can reveal the recipient when decoded, just as the public chain can.

```bash
python3 tools/check_wallet_privacy.py --self-test
./release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 tools/test_v5_refund_cleanup.py
```

The hash-based privacy check runs in the release-facts GitHub workflow and does
not embed the retired identifier. The refund regression replays the archive and
rejects altered pins, destinations, amounts, closure balances and fees.

## Retention limits

Branches and tags can be rewritten; GitHub's retained PR refs cannot be changed
through a normal push. PRs #3–#9 retain affected historical ancestry and need
GitHub Support to remove cached views/references and garbage-collect old objects.
Forks, existing clones, search indexes and immutable Solana transactions are
outside this repository's control. Recovery backups must stay private and must
never be pushed back into public history. Collaborators should clone the cleaned
repository or rebase unpublished work onto it, rather than merge old history.
