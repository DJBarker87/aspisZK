# Adoption of the compact binary-multiproof proof format (2026-10-19)

Pre-registration: `design/PREREG-PROOF-SIZE-2-20261019.md` (items 1, 3, 4,
5, 6 here; item 2, the worst-case bound re-run, is a separate job).
Prototype: `evidence/proof-size-20261019/` (feature `compact-binary`).
Base: `research` at 931d81273. Branch `codex/r1-format-adopt-20261019`.
Host work dir: `/home/dombarker/project-offloads/codex-r1-format-adopt-20261019`.

UNPROVED: none of this is a security claim until the obligations in
`design/PROOF-SIZE-OBLIGATIONS-20261019.md` close.

## Verdict

(pending)

## 1. Source change (item 4: shipped default build)

`crates/aspis-r1-cost-probe` (the prototype's `compact-binary` feature is
removed; its code is now the default):

- `verifier::{tx1, tx2, tx2_authenticated, parse_shape}` are the compact
  binary-multiproof verifier (`candidate.rs`, re-exported), with
  `verifier::PROOF_BYTES = 57,607` and `verifier::SPLIT = 10` (stage 1
  accepts only split 10). These are the only R1 verification entrypoints of a
  default build. `View::proof_bytes` is renamed `View::eight_way_proof_bytes`
  (a layout figure for the retired format).
- The eight-way verifier (`View::parse`, per-query paths, `query`,
  `tx1/tx2/tx2_authenticated`) is moved unchanged into
  `verifier::eight_way` (`eight_way.rs`), compiled only with the new
  audit-only feature **`audit-eight-way`**. It never replaces a default
  name. `lib.rs` makes it a `compile_error!` together with `prover`, or on an
  SBF target (`target_os = "solana"`); receipt `guard-audit-with-prover`
  shows the error. `private-leaf-salts` is now a default feature (the
  adopted format is defined only over salted leaves; building without it is
  a `compile_error!`), and `prover` implies it.
- Prover: `prove_from_semantics` is the prototype's compact prover (binary
  C1/C2/folded trees, compact semantic/`y1`, six zero-padded node slots);
  the eight-way and unsalted prover bodies are deleted, `Commitment` is
  binary-only, and `prove`, `prove_masked_fixture`, `prove_masked_attempt`
  and the retry loop `prove_masked_retrying[_with]` keep their signatures
  and emit only the new format (the `_candidate` entry points are removed).
- `dense.rs` reads the compact format with its own expansion, canonical
  scan and BTreeMap multiproof reconstruction (independent of the verifier's
  batch code; layout constants from `compact`).
- `sim.rs` (simE) still programs eight-way paths and emits the retired
  layout. Its two tests are `#[ignore]`d with a note citing
  PROOF-SIZE-OBLIGATIONS item 5 (section 6); nothing is deleted.
- Examples: `proof_size_s2` (teeth) is re-pointed at the default build (its
  eight-way control is a saved eight-way fixture); split 11 -> 10 in
  `masked_fixture_gate` (S2 only), `secure_attempt_gate`, `r1p_retry_gate`;
  `authenticated_tx2_gate` uses the compact opening offset. `proof_size_s1`
  and `native_gate` read or mutate the eight-way layout with the prover; they
  now require `prover` + `audit-eight-way`, a forbidden combination, so they
  are retained for the record but not buildable.

`programs/r1-cost-probe`: the `compact-binary` feature and the adapter shim
are removed; the adapter uses `verifier::PROOF_BYTES` and
`verifier::parse_shape`; `lib.rs` asserts `PROOF_BYTES == 57,607` and
`SPLIT == 10` at compile time. The release feature set is unchanged
(`pool-adapter,private-leaf-salts`). `[3, 11]` remains an admitted route; its
verification now always rejects (tested, no account written).
`r1_checkpoint_tests.rs` uses the regenerated transfer-1023 fixture; the
hash-call counts are asserted by a closed form (per batch and tree, three
leaf hashes per query plus `nodes + distinct - 1` parent hashes), and the
zero-progress checkpoint (`next = 0`) is now rejected by stage 2 after the
three resume hashes (the adopted stage 2 requires `next == SPLIT`).

`tools/r1-hash-input-counter`: default = adopted verifier (split 10);
feature `audit-eight-way` = eight-way verifier (split 11). Its `Cargo.lock`
loses the three optional-dependency edges of the removed `prover` feature
(fetched once, receipt `counter-fetch`).

The Pool program source is unchanged.

## 2. Fixtures (regenerated)

The six saved fixtures (`aspis-r1-rollover-measurement-20261019/fixtures/*`,
eight-way, 124,343 bytes) were re-proved with the adopted default prover:
same witness (`--pairs N`, kind), fresh OS entropy, split 10, by the
measurement driver (section 3). In every run the generated ASF8 statement
equals the saved fixture's statement byte for byte (`PROOF_SIZE_PUBLIC_MATCHES`
in each `receipts/adopt-*/stderr.log`; `public_equal_saved_fixture` in
`cu.json`), and the default verifier (tx1 split 10, strict tx2,
authenticated tx2) and the dense verifier accept natively before the SBF
replay. The new proofs and statements are committed under `fixtures/`
(proof data, 57,607 + 1,880 bytes each; the program checkpoint tests
include transfer-1023):

| Fixture | Proof bytes | Proof SHA-256 | Statement SHA-256 (= saved) |
|---|---:|---|---|
| transfer-13 | 57,607 | `55386c507d3feeeb...` | `f6bcd49446f1077d...` |
| transfer-255 | 57,607 | `fbc921ceb417aa22...` | `e201be4a028d7425...` |
| transfer-1023 | 57,607 | `832b4ae1a90c6e34...` | `72f067d263af326b...` |
| withdrawal-13 | 57,607 | `86623038d33f7fef...` | `43b4235fd9752c40...` |
| withdrawal-255 | 57,607 | `d92a261b2ba10c97...` | `7c2c27e135fa5377...` |
| withdrawal-1023 | 57,607 | `1c200eacfd8ea117...` | `456bcde525f9e694...` |

## 3. Compute (item 1)

(pending)

## 4. Uploads (item 6)

(pending)

## 5. Standing gates (items 3 and 5)

(pending)

## 6. Pins

(pending)

## Runs

Receipts under `receipts/` (command, exit, wall, peak RSS, swaps, cgroup
limits) per host run. `#print axioms`: N/A, no Lean in this job.
