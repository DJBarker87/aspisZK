# NDZ retained public identities

No secret bytes were printed, copied, hashed or committed. No key was deleted.

Devnet payer (read-only):
`~/.config/solana/aspis-deploy/devnet-payer-20261029.json`, mode 0600,
CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t, 18.35320408 SOL at inspection.

Fresh devnet verifier identity generated only after the identity gate passed:
`~/.config/solana/aspis-deploy/NDZ_release-20261029/verifier.json`, mode 0600,
CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ.
Its containing directory is 0700, outside workspaces/offloads. No public-cluster
transaction or signature has been sent for it. The key remains on the Mac.

Local rehearsal root on dombarker@100.108.41.90:
`/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/evidence/devnet-rehearse-20261029/keys/`.
Keys and all validator ledgers are retained beneath this private 0700 root.
The repository evidence `.gitignore` excludes `keys/` at the same relative path.
Local payer: JDBfF4zrTqddwXJsVEFjjMBAx8f5SDHCf8GcCzZikx4R.
Local verifier: BWqJ6cr2ZYpg2LaBHacX5vfaZXczVMMcv8u18H7GetMx.
Local buffer: 4m5wfNhebGF5ektKtUyegvprjSiZpij75S4SacDpDRBV.
Fixture and proof-selection keys are generated beneath that same keys root;
public mapping is retained in the receipts. Do not clean the host task directory:
keys control local funds, tokens and authorities, including in the abandoned
but retained default-feature ledger.

The intentional signer failure and interrupted default-feature attempt each
closed their buffer to the local payer, confirmed finalized zero balance and
recorded an empty buffer list. The buffer key is retained and reused on the
fresh devnet-feature ledger. No public SOL was affected.

The final ledger is keys/NDZ_final_ledger (RPC 18995 during execution). The older
keys/NDZ_ledger and keys/NDZ_devnet_features_ledger remain intact. All validator
processes are stopped after receipt capture; no ledger or key was removed.
The final small buffer-failure probe uses keys/NDZ_failure_final/, also retained.
NDZ_LOCAL_KEYS_PUBLIC.json lists 31 workflow key files by public identity/mode;
validator internal keys and retained generation aliases remain in their private
ledger/proof directories and were not copied or hashed.

Eight additional unfunded, local-only nonce-account keypairs were generated on the
Mac in evidence/devnet-rehearse-20261029/keys/NDZ_writer_offline/ for the offline
writer proof-generation check. That gitignored private directory and its nonce
store/proof artifacts are retained. NDZ_WRITER_PROVE_RESULT.json records public
identities only. The container had networking disabled and no devnet key mounts.
