# J1 split-checkpoint Pool handoff (2026-10-16)

This is a source and artifact inventory for the current `aspis-pool` split-checkpoint path. It does not change Pool code and does not claim a current Pool SBF or transaction-level settlement replay.

## Current source interface

Reviewed checkout: `/Users/dominic/ZK/.worktrees/r1-terminal-copy-indexed-20261016`, HEAD `a8930e677bc745854b9f693b5628c8a8bd2ac848`. The three Pool-owned files are unmodified in this worktree. Current SHA-256 pins:

- `programs/aspis-pool/Cargo.toml`: `80b82887fd0c50e1e9f5e76cd9c3fe6e4c721e64692d418dd6a9b845b2f5e05d`
- `programs/aspis-pool/src/pair_forest.rs`: `2e0852f4c5dc7ba0b25ac1567b8c3e7c3a52c8038685dad34ec2f29e05eec957`
- `programs/aspis-pool/src/pair_forest_dispatch.rs`: `95f1d6188c6102ab5724cd9791e96d77c519cb3e88dba09a52532f7882f43ad8`

`r1-split-checkpoint` is declared at `Cargo.toml:26-29` and is not a default feature. It enables `pair-forest-verifier-lane-invariant-audit`, which in turn enables `pair-forest-account-evidence`. In `pair_forest.rs:1085-1093`, the layout keeps the legacy transfer/withdrawal token indices and appends one verifier-checkpoint account after the full legacy list; exact length and key uniqueness are checked. For rollover, the legacy root-page layout first consumes its additional page slot (`pair_forest.rs:1049-1076`).

With the feature enabled, `pair_forest_dispatch.rs:90-120` accepts a foreign proof buffer only when it is non-executable, non-signer, read-only, distinct from the verifier program, and requires the separate verifier checkpoint to be owned by the selected verifier, non-executable, non-signer, read-only, and distinct from the proof/verifier. `:124-140` checks it is not the Pool master, Pool checkpoint, selected lane, or either registry account. The CPI forwards both as read-only accounts (`:311-363`), placing the extra checkpoint after registry/entry and before the verifier program in the account-info list. Unit assertions at `:1088-1159` check alias rejection and the forwarded account position.

The real terminal processor is already present: `pair_forest.rs:1396-1512` decodes state/request, plans the account layout, reserves the nullifier marker, and calls the selected verifier with the optional appended checkpoint. It then validates the authenticated result; the continuation performs optional withdrawal token CPI and checks its exact delta before writing lane/page/marker and return data (`:1513-1585`). The ordinary entry is `process_pair_forest_terminal_v1` (`:1588-1605`). The full-ASF8 entry is audit-gated (`:1608-1675`). Therefore the Pool source has the intended transaction integration surface; the open item is a matching built/replayed artifact with actual accounts, not implementing the feature from scratch.

## Retained evidence and its limits

| Evidence | Recorded result | What it establishes |
|---|---|---|
| `evidence/g-r1-8-native-20261015/g8-pool-dispatch.json` | `cargo test --release -p aspis-pool --features r1-split-checkpoint,pair-forest-source-result-invariant-audit,pair-forest-deposit-invariant-audit ... pair_forest_dispatch::tests`; exit 0; 4 tests passed; source hashes match all three current Pool pins above; revision `5cbd3f9a24b4446d413d38c33ec1d703b210fd16`. | Exact-source native dispatch/layout/account-forwarding tests. Uses mock runtime; not SBF or an actual Pool-to-verifier transaction. |
| `evidence/g-r1-9-pool-native-20261015.json` | Six focused checks at `185d576e5e7f2e2aee01db7ddb1d74b09d77cc6a`; split-feature dispatch (4 tests) and terminal (4 tests) passed, plus active V7 comparisons and full-ASF8 compile-only. | Earlier native coverage. The recorded `pair_forest.rs` / `pair_forest_dispatch.rs` hashes differ from current pins, so treat as predecessor evidence, not current-source receipts. All are native/mock or compile-only. |
| `evidence/g-r1-8-native-20261015/g8-r1-checkpoint-c.json` | Release native tests in `aspis-r1-cost-probe-program` with `pool-adapter,private-leaf-salts`; 23 passed. | Verifier adapter checkpoint behavior (including owner/flags/size, aliasing, raw-buffer checks); this is not `aspis-pool`'s `r1-split-checkpoint` feature or Pool settlement. |
| `evidence/p3-private-leaf-salts-20261013/p3-pool-13/` | Older `pool_gate` SBF built with `pool-adapter,private-leaf-salts`; transfer fixture-control at 13 pairs passed. | Retained older P3 transaction/runtime exercise. Its program/ABI/source pins do not identify the current `aspis-pool` feature build and cannot substitute for it. |
| `evidence/pool-v1/` and `evidence/pool-adapter-v4-k11-20261013/` | Older cost-probe/pool-adapter SBF artifacts and stack reports. | Historical adapter artifacts; no matching current `aspis-pool` `r1-split-checkpoint` source/feature fingerprint was found. |

Search of retained `evidence/**/*.json` for SBF build receipts found no `cargo build-sbf` receipt for package `aspis-pool` using `r1-split-checkpoint`. The retained SBF receipts are for `programs/r1-cost-probe` / `pool_gate`. The focused G_R1.8 full `pair_forest::tests` attempt was not an all-green suite (23 passed, one unrelated canonical-bump test failed); the later exact-source G8 dispatch target passed. Do not turn that partial history into a full Pool regression claim.

## Concrete next validation work

Use the current candidate verifier ELF and the current Pool source to prepare a dedicated LiteSVM transaction harness. The harness should build the `aspis-pool` SBF with `r1-split-checkpoint` (and the necessary account-evidence dependency, transitively enabled), pin its ELF and all selected verifier/registry ELFs, provision a registry entry and verifier-owned checkpoint, and exercise the actual Pool terminal instruction rather than call its internal plan/dispatch functions with a mock runtime.

The transaction fixture needs both private transfer and withdrawal. It must construct the Pool-owned master/checkpoint/lane/history pages, marker, payer/system accounts, registry+entry, executable verifier account, foreign read-only proof buffer, and final read-only verifier-owned checkpoint in the exact account order. Withdrawal includes its five custody accounts before the appended verifier checkpoint; rollover includes the next root-history page before the trailing checkpoint. Successful runs should compare lane/page/marker images and, for withdrawal, token-account balances against expected outputs; verifier checkpoint bytes should remain unchanged during terminal CPI. Include at least one rejected proof/checkpoint case and confirm Solana transaction rollback preserves state.

Existing `pair_forest.rs` unit tests provide reusable fixture intent but mock the verifier runtime. Existing P3 `pool_gate` fixtures are reusable only after their account image, instruction ABI, and program ELF are explicitly reconciled to this current feature. The current `r18_replay` evidence is verifier-focused and does not itself prove Pool lifecycle/settlement behavior. Keep native verifier-only runs labelled separately from Pool transaction settlement.
