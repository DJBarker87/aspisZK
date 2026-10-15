# Lead review of the J1 continuation (64bbb8fc2, 95bf664bc) and the entrypoint decision

Merged into `codex/100bit-spend-path-20261013` as 7dc4addc8 (no file overlap
with the live sessions' commits since 136b74680).

## J1.R6 Accepted

- J1.R2 is closed: `SpendAppendBinding.lean` is the lead-fixed statement
  verbatim, it is the sixth conjunct of `Rspend`, and `appendCheck_eq_true_iff`
  and the extraction carry it (1aca98e95, 136b74680).
- Public descent (`PublicBaseProjection`), the §9 public-byte codec with
  `parseRaw ↔ encode`, `decode ↔ encode ∧ check`, completeness for canonical
  statements with index < 2^64, strict rejection of truncations, suffixes and
  bad tags, and lengths 1455 / 1427 — accepted. The Rust field order match is
  inspection; J1.a turns it into a theorem.
- `TypedPrefixParser` and `SemanticPrefixCodec` (25 payload rows, round trip
  both ways, prefix stability) — accepted as completed-record laws. The
  row-0 warning (payload row indices are not Unified row indices) is binding.
- The `R1SemanticPayloadView` source-pin repair closes the gap noted in
  J1.R4 of the first review.

J1 remains open on J1.a–J1.e exactly as listed in `J1-R4-STATUS-20261015.txt`.

## J1.R7 Decision: the oracle model and the hash-input bound

The FS oracle in the soundness theorem is a random oracle on **all finite
byte strings** (`Bytes → Digest`). The collision term `12·Q²/2^256` and the
per-query terms are per call and do not depend on call length, so no uniform
input-length cap L is needed for soundness. Consequences:

1. `pool_calls_fit` / `CallsFit L` is **not** a soundness obligation. It is
   kept, if at all, as an engineering check (CU and heap), not in the ledger.
2. `CanonicalByteHash`'s overlength fallback (encode to the empty address) is
   removed from the oracle model used by the theorem: the theorem's oracle
   must hash every input, of any length, to an independent value. Where an
   existing lemma needs a bounded encoding, it takes the length as a premise
   discharged by the parsed shape of that call, not by a global L.
3. What remains mandatory is the **count**: QV, the number of designated
   oracle calls one verifier execution makes, proved for every input on the
   admitted routes, including rejections, panics and allocation failures
   (prefix-closed, as in the proposal's `SourcePrefix`). Qtot = QA + QV·(number
   of verifier executions charged) stays as decided.

## J1.R8 Decision: admitted entrypoint scope

The soundness theorem covers the deployed program's whole instruction surface.
A route that is reachable on chain and not in the theorem is a hole, not an
exclusion. On the current source (`programs/r1-cost-probe/src/lib.rs:31-37`),
with `pool-adapter` enabled, the legacy routes `[1,k]` and `[2]` remain
reachable, and `[1,k]` writes a program-owned checkpoint account from
arbitrary `public` and `proof` accounts. That contradicts the trusted
precondition of decision 1 ("checkpoint written only by tx1 after strict
parsing") for any checkpoint the pool route reads, unless the pool route
provably rejects checkpoints the legacy route can produce.

Decision:

1. **Admitted routes (the theorem's scope):** `[3,10]`/`[3,11]` →
   `r1_pool_adapter::stage1` → `verifier::tx1`, and `ASQ8…` → `stage2` →
   `verifier::tx2_authenticated`, under the pinned configuration of
   `J1-CONFIG-BOUNDARY-PROPOSED-20261015.txt` §1.
2. **Source guard required:** the release configuration must reject every
   other instruction byte before any account is read. The legacy `[1,k]` and
   `[2]` branch is removed from any build with `pool-adapter`, or placed
   under a feature that the release pin cannot enable. This is a code change
   for the spend-path sessions and becomes gate item G_R1.7. Until it lands,
   the scope is a premise and the J1.e theorem carries `hroute : PoolRoute
   i.data` explicitly.
3. **Lifecycle routes 4/5/6:** they reach `r1_pool_adapter::process`. Before
   release, each is either (a) shown not to write any account that stage1 or
   stage2 trusts (checkpoint, statement, proof buffer) and not to call the
   designated oracle, or (b) brought into the theorem. The proof bytes
   immutability premise of decision 1 is discharged here or not at all.
4. **Direct helpers** (`checkpoint`, `resume`, `Transcript::*`,
   `Prepared::new`) are internal: they are covered only through the admitted
   routes, with their argument lengths given by the route's parsed shapes. No
   separate theorem for arbitrary inputs.
5. **Runtime / PDA / CPI SHA-256.** If the designated oracle is SHA-256
   itself, every SHA-256 call is an oracle query. Adversary calls are in QA.
   Verifier-side PDA derivations on the admitted routes are counted in QV
   with their fixed shapes; they cannot be dropped by domain argument unless
   the designated oracle calls carry a domain prefix that no PDA input can
   produce, proved from the byte formats. The J1.e count states which.

## J1.R9 Order

J1.a–J1.e continue as listed, with J1.e restated as the QV count under
J1.R7–J1.R8. G_R1.7 (route guard) is issued to the spend-path sessions in
parallel; it does not block J5 ∥ J2, which may start once J1.a and J1.b land.
