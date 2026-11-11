# Pool payout path: predictions made before any Pool run

Written from reading `programs/aspis-pool/src/{vault,pair_forest,pair_forest_dispatch,registry}.rs` at
4045ecbdda3 (the Pool sources are those of b936275, unchanged). No tool had been run on the Pool crate when this
was written. Feature set to be used: `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
(the set named for the R1 Pool build in `design/R20-POOL-HANDOFF-AUDIT-20261020.md`, line 154; to be confirmed
against the deployed build by the lead).

| Function | Constructs seen | Prediction |
|---|---|---|
| `vault::require_zero` | `bytes.iter().any(closure)` | translates with standard-library items external (80%) |
| `vault::token_array` | `bytes.try_into().map_err(closure)`; const generic | translates (80%) |
| `vault::parse_coption_pubkey`, `parse_coption_u64` | straight-line, `match` on a `u32`, `Pubkey::new_from_array` | translate (85%) |
| `vault::parse_legacy_mint_v1`, `parse_legacy_token_account_v1` | straight-line with `?` | translate and elaborate (80%) |
| `vault::require_token_owned_account` | reads fields of `AccountInfo` | fails while `AccountInfo` is opaque (R1's "non-adt type" error) (85%) |
| `vault::exact_five_withdrawal_accounts` | slice pattern with `else`; `return Err` inside a loop inside a loop; `AccountInfo.key` | fails: return in a nested loop (95%) |
| `vault::pool_v1_vault_authority_address`, `registry::stored_bump_address_matches` | one SDK call each (`find_program_address`, `create_program_address`), `is_ok_and(closure)` | translate with the SDK call external (75%) |
| `vault::plan_legacy_withdrawal_transfer_from_identity_v1` | `AccountInfo` fields; `try_borrow_data()?` guards; `vec![AccountMeta…]`; `Instruction`; no loop | fails while `AccountInfo` is opaque (85%); would need `AccountInfo` field reads and the data borrow behind stated boundaries |
| `vault::validate_exact_withdrawal_delta_v1` | as above, two data borrows | fails for the same reason (85%) |
| `vault::exact_withdrawal_transfer_account_infos_v1` | `AccountInfo::clone` five times | fails or needs `clone` external (70%) |
| `pair_forest::validate_pair_forest_request_accounts_v1` | `AccountInfo.key`; `match` on the payment enum; long `||` chain; `1u8 << output_lane` | fails while `AccountInfo` is opaque (75%); the logic itself has no loop |
| `pair_forest::process_pair_forest_terminal_with_verifier_v1` | generic over a runtime trait and two `FnOnce` parameters (one with eleven arguments); three `try_borrow_mut_data` guards held across the token call; `AccountInfo` throughout | fails (95%): closure-typed parameters under the second pair, account wrapper class under either |
| `pair_forest_dispatch::plan_pair_forest_terminal_dispatch_v1` (request re-encoding) | one encoder call, `.to_vec()`, then a call | translates with the callee opaque (60%) if `AccountInfo` appears only in its signature |
| `pair_forest_dispatch::invoke_pair_forest_terminal_with_runtime_v1` (dispatch and return-data read) | `vec![…]` of `AccountMeta` and of cloned `AccountInfo`; `infos.insert`; trait-method calls on the runtime; `Option<(Pubkey, Vec<u8>)>` | fails while `AccountInfo` is opaque (75%); the return-data handling after the call is straight-line |

Expected overall: the pure parsers and the address helpers translate; every function that touches an account
fails in the same way R1's `stage1`/`stage2` do, and the remedy to examine is a boundary (opaque callee with a stated
specification) rather than a change to the Pool.
