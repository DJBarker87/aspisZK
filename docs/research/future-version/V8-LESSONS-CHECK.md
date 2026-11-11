# Aspis one-transaction verifier: check against what went wrong in V8

2026-11-11. Owner instruction: look at what went wrong with soundness and privacy in V8 and
make sure the one-transaction version, which is a new version and is called Aspis, does not
repeat it.

Sources for V8: `docs/research/v8-audit-20261005/` (DECISION.md, B_SOUNDNESS_100.md,
A_MASK_COVERAGE.md, CONVERGENCE.md) and the lessons section of AGENTS.md. "R1" below means the
existing two-transaction verifier at the PIN2 pin; "Aspis" means the one-transaction verifier on
this branch.

Nothing in this note establishes soundness or privacy of Aspis. It records where the V8 failure
patterns were looked for, what was found, and what is still open.

## Finding 1: the pinned numeric bound does not carry over (corrects an earlier statement)

The R1 claim is `total(Q) = (Q+34)·B + collisionLoss(Q) + accountLoss(Q) + 2^-126 + 2^-454`
with `B = 15/2^109`. `B` is a common envelope charged to every transcript start, not a sum over
rows. At `Q = 0` the R1 bound is `34·B = 510/2^109`, and the contract's criterion (A),
`total(0) < 2^-100`, holds with a margin of about `2^-108`, which is `2/2^109`.

Aspis adds seven transcript rows (the combining challenge and six sumcheck rounds). One more start
at the common envelope already exceeds the margin. With 41 starts the same accounting gives
`41·B = 615/2^109`, about `1.2 · 2^-100`. No common envelope repairs this, because the query row
alone is about `14.5/2^109` and `40 · 2^-105.14 > 2^-100`.

Consequences:

- The statement in SOUNDNESS-ROWS.md that the pinned form "keeps its largest row" is wrong as a
  description of the proved theorem, and the lead's statement to the owner on 11 November that
  "the headline figure should not move" is withdrawn. Under the pinned accounting Aspis misses
  criterion (A).
- The seven new rows have caps near `2^-120` each. An accounting that charges each verifier
  start its own row's cap, and each adversary query the largest cap, would give roughly
  `Q·B + B + (small terms)`. That is a different composition theorem. It does not exist. Whether
  the pinned Lean development can be generalised to it is not known.
- Until such a theorem is proved, the honest position is: for Aspis there is no per-attempt
  figure, and the pinned theorem's form does not extend to it.

This is the V8 pattern of quoting per-row errors as if they were the composed bound (audit gap B6,
AGENTS.md section 2). It was caught before any claim was published.

## Finding 2: what the proof binds, checked by test

`crates/aspis-r1-cost-probe/tests/aspis_one_tx_statement_binding.rs` (new; 2 tests, both pass):
over the six saved fixtures the re-packed proof verifies against its own statement and is rejected
against a statement changed in any one of: pool, deployment domain, withdrawal destination,
withdrawal amount, recipient commitment, change commitment, nullifier, anchor root, asset id,
source next pair index, source frontier, afterstate root, afterstate frontier (69 cases). The
binding tail added at PIN2 is therefore active on the one-transaction path.

Two statement fields are outside the transcript bytes, as in R1:

- source sequence number: a change is rejected by the guard that requires it to equal the next
  pair index;
- source current root: a change is ACCEPTED by the verifier function. The proof does not bind it.
  The one-transaction entry does not take it from the prover: it rebuilds the lane snapshot from
  the authenticated lane account (`r1_pool_adapter_owned.rs`, the snapshot built before
  `reconstruct_asq8_statement`). No use of the proof for that field was found. It is recorded here
  because an unbound field is how the withdrawal-destination problem arose.

Bytes of the proof that are neither absorbed nor checked: none found. Unused multiproof slot bytes
must be zero, reserved header bytes must be zero, certificate limbs must be canonical (existing
tests change padding and certificate bytes and expect rejection). The soundness agent is asked to
confirm this independently.

## V8 soundness failures and Aspis

| V8 failure | Where it could recur in Aspis | Status |
|---|---|---|
| Round targets valid only for a family "fixed before the challenge", with no theorem that it is fixed (gaps B1, B2); the unconditional form was refuted | Every new or changed row: the two residual families under the batching challenge, the two claims under the combining challenge, each round polynomial under its round challenge | OPEN. The residuals are functions of opened values bound to three roots and of challenges drawn earlier; the claims and round messages are absorbed before their challenges (read from the code, not proved). The soundness agent builds the ledger from the code and attacks it. |
| The channel fold made "queries test only the combination" and added an extraction obligation that was never closed | The batched first-fold check tests only a combination of the 22 residuals | Different in one respect: the combining challenge is drawn after the combined values are fixed, and R1 already batches the second-fold residuals the same way. Proved: the algebra only (`TwoFamilyResidualBatch.lean`). OPEN: the bridge from authenticated openings to the residual vectors, which R1 has for one family and one tree and Aspis needs for two families and three trees. |
| A compact round encoding where reconstructed and true polynomials agree at one challenge value, an event never charged (R547, R548) | The final sumcheck reconstructs the linear coefficient from the running claim | OPEN. Each round is charged two bad challenges, which is meant to cover every coincidence; the agent is asked to model the reconstruction exactly as coded, including challenge values 0 and 1. |
| No Fiat-Shamir theorem for the actual transcript; published theorems cited from memory | The 40-row transcript | OPEN, and worse than first stated: see finding 1. No theorem is cited from memory in the agent's brief; it proves what it uses or marks it open. |
| Earlier theorems assumed to apply to new objects without being re-bound | Every R1 theorem reused for rows 0 to 32, the extractor and the collision terms | OPEN. They are theorems about the R1 source and the R1 game. Aspis has a different entry, different loops and one transaction. Reuse needs a stated mapping from an Aspis proof to R1 data, which is written in prose only. |
| Closed lemmas about fixed mathematical objects, no model of the verifier; progress counted in theorems | The Lean files on this branch | The one compiled lemma is labelled algebra only. No count is used as progress. |
| Ambiguous meaning of "100 bits" | Any figure quoted for Aspis | No figure is claimed. Criteria (A) and (B) of the contract are the only readings used. |
| Performance redesigns that each needed new cryptographic repair | Aspis exists to fit a compute limit; it changes the acceptance predicate and adds a sub-protocol | This is the central risk and it is real. The new obligations are finite and listed (SOUNDNESS-ROWS.md, and the agent's note when it lands). The owner should weigh adoption against finding 1. |
| Sources and artifacts outside the tree | Verifier ELF, client, scripts | In the branch and pushed; ELF hash and build record kept. One build only: no independent rebuild for reproducibility has been done. |

## V8 privacy failures and Aspis

| V8 failure | Where it could recur in Aspis | Status |
|---|---|---|
| Published values not covered by the masking argument; each redesign added published values | The certificate (twelve values) and the merged multiproofs | The re-pack function takes the pinned proof and the public statement and nothing else, so everything it adds is a function of data already published; the merged multiproof nodes are a subset of the pinned proof's nodes. The statement account and the stage 1 checkpoint are no longer published. Stated, not proved: "a public function of a simulatable view is simulatable" is one lemma, to be written when the privacy proof for the pinned prover exists. |
| The construction validated in tests was not the one the theorems covered | The devnet runs used the planner's re-pack on the pinned prover's output | Same function by construction. It stays true only while the release client calls exactly this function as a separate step. Folding it into the prover would move the privacy pin. |
| Freshness and independence assumed silently; retries and aborts not shown witness-independent | (a) The one-approval flow makes a fresh session key the base of the seed-derived accounts, and the proof account address is the prover's public mask nonce. (b) The re-pack and the local check can fail. | (a) ANSWERED WITH A CONDITION by the privacy lead (2026-11-11), not proved for Aspis. In `lean/PV_SK_Headline.lean` (branch codex/pv-seedkeys-20261111, dcb6fd8b7ef) the base, the owner program and the tag are universally quantified, so the nonce statement and its reject-mass bound hold for every fixed base and therefore on average over a random session key. Condition: base, owner program and tag must be chosen independently of the witness and of the oracle. For this flow the session key must come from the OS generator and nothing else; a session key derived from wallet or note material would break the condition. The seed must stay `p{k}` plus 30 hex characters with a 32-byte owner (the 96-byte length and injectivity in k are used). The run script meets both (`solana-keygen new`; the PIN2 seed layout). Still open, as at PIN2: the theorem's premise that the client's nonces equal the oracle values at those addresses. (b) The re-pack cannot fail on a well-formed pinned proof (argument in the code comment and the slot-bound tests); a failure would abort before anything is published. |
| Only one witness difference tested; "no separator found" treated as evidence | Nothing | No privacy test was run for Aspis and none is claimed. |
| No numerical privacy bound assigned | The per-proof privacy figure | Unchanged if the post-processing lemma holds; not claimed otherwise. |
| Side channels | Timing of the re-pack; upload pattern | The re-pack runs on public data. Every payment sends the same number and sizes of transactions. Measured, not proved, as for R1. |

## Actions taken

1. Finding 1 sent to the soundness agent with instructions to verify it from the Lean source and
   lead its note with it; sent to the soundness lead.
2. Statement-binding test added and run.
3. The V8 failure list sent to the soundness agent as explicit cases to test.
4. The nonce-base change sent to the privacy lead; answered the same day with the condition recorded in the table above.
5. SOUNDNESS-ROWS.md marked with the correction.

## Naming

From 11 November the one-transaction version is called Aspis in prose. Identifiers that still
carry experiment labels are listed here so they are renamed at the next build and not before (the
devnet verifier is immutable and its source must stay as recorded): the proof format magic
`R1F1SM22`; the module `fused` and its `*_summed_format` functions; the `future-*` cargo features;
the crate and program names ending in `cost-probe`; the transcript domain, which should be decided
together with version separation. Directory and script names under `future-version` and `FV_`
stay as labels of this evidence.
