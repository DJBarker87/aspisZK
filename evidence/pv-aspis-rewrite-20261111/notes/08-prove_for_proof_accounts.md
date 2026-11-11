# 8. `prove_for_proof_accounts` (client entry)

File: `crates/aspis-r1-cost-probe/src/RealR1_client.rs` (module is
`#[cfg(feature = "r1p-check")]`).

## How the callback is called today

`prove_for_proof_accounts` passes a closure to `prove_masked_retrying_with`; the
retry loop calls it once per attempt entered, for k = 0, 1, ... in order, just
before that attempt's nonce reservation, and never for an attempt that is not
entered. It is lazy. The function's own documentation says so ("for each entered
attempt", "keys may be chosen after prior attempts").

Callers in the tree, and what their callbacks do:

| caller | callback | pure? |
|---|---|---|
| `tools/r1-cost-probe/src/bin/devnet_spend/plan.rs` line 120 | `\|k\| accounts.nonce(k)` (`Client64_accounts.rs` line 27): asserts `k == self.entered`, returns `keys[k]`, increments `entered` | no: it counts the calls. The keys themselves are fixed before the call |
| `crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs`, `fixture` | draws a fresh random address per call and records it; the test then requires `addresses.len() == result.attempts` | no: one OS draw and one record per call |
| same file, the repeated call | `\|_\| addresses[result.attempts - 1]` | yes |
| `tools/r1-cost-probe/src/bin/pv_client_gate.rs` line 747 | `\|_\| selected.to_bytes()` | yes |

So a wrapper that asked for all eight keys first would change what two of the four
callers observe (the call count in the planner's bookkeeping, and the test's
`addresses.len() == result.attempts`). Eager evaluation is not equivalent here.

## What was done

`prove_for_proof_accounts` is unchanged, byte for byte. Two functions were added
beside it:

* `prove_for_proof_account_nonces(public, compiled, hash, nonce_store, nonces:
  &[[u8; 32]; ATTEMPT_CAP])`: the first-order entry for a caller that fixes the
  eight keys before proving.
* `prove_for_proof_account_nonces_timed(.., times)`: the same without the
  thread-local timing store (see note 6); this is the one to translate.

Both run the same retry loop (`retry_attempt`) through a private provider struct
`ProofAccountNonces` whose `attempt_secrets(k)` is
`StateOnlyAttemptSecrets::generate_for_mask_nonce(self.nonces[k]).map_err(|_|
Error::Entropy)`, the body of the closure in `prove_for_proof_accounts` with
`proof_account(k)` replaced by `nonces[k]`. The loop calls it only for `k <
ATTEMPT_CAP` (the cap test comes first), so the index is in range.

The new entry equals the old one for a callback that returns `nonces[k]` and does
nothing else. It is not used by any existing caller. The planner already holds its
eight keys in an array before the call and could use the new entry, but its
`entered` counter and its self-test on the text of the call would have to change
with it; that was left alone.

Test added: `nonce_array_transfer`, `nonce_array_withdrawal`
(`RealR1_client_tests.rs`): only the entered attempts reserve a nonce, each its
own; the proof verifies; one check record per attempt; the `_timed` form fills the
explicit log and leaves the thread's store empty; a second call with the same keys
fails closed with `Semantic`.

## Option not taken

Making `prove_for_proof_accounts` a wrapper over the array form needs either an
eager callback (changes observable behaviour, above) or a new contract for the
callback ("called eight times before proving"), which is a change to a public
function that the devnet client uses. That is a decision for the owner of the
client.
