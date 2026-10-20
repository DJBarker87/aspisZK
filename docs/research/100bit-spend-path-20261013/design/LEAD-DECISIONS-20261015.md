# Lead decisions on the parallel R1 design proposals (2026-10-15)

Dated note (2026-10-20): the [binary-multiproof ledger amendment](../../v8-r1-20261011/R1_SOUNDNESS.md#amendment-for-the-binary-multiproof-format-2026-10-20)
records the adopted frozen format, binary collision allowance, verifier query
budget, query-scan abort, privacy read budget and successful stage-1 route,
with source and proof evidence. It preserves the earlier text as history and
states the remaining refinement conditions.

Inputs: `CLASSIFIER.txt`, `KNOWLEDGE.txt`, `TERMINAL-D3.txt`,
`PARALLEL-REPORT-20261015.txt` (this directory), reviewed by the lead. The
three proposals are **accepted as designs**; nothing in them is a proved
result. The source corrections in the report (challenge schedule rows 0–24
semantic, 25–26 circle, 27–30 γ/κ/α₀/α₁, 31 q22, 32 ρ; fixed-word caps do not
transfer to existential classifiers; FS2.D3 is unconditional in H and T;
`extractFails` reads the table before row 0; collision budget is
`12·Qtot²/2^256`, charged once; overlength hash inputs map to the empty
address) are accepted as binding.

Security target (`TARGET-CLARIFICATION-20261015.md`): 100-bit per-attempt
soundness, no grinding credit; the query-dependent statement
`Q·max_row + collision` is retained and is the standard reading.

## Decision 1 — relation and trusted preconditions

- `Rspend` is executable and is the conjunction of: the R0 semantic relation
  (`sourceData.paymentWitness`, Pair Forest) on the public statement; input
  note membership in the tree at the statement's anchor; knowledge of the
  note's secret key and salt (`R0P.input_note_extracted` form); nullifier
  derivation; bounded value conservation; output note commitments; the
  statement's canonical options. `SpendSemantics.NoteFacts` alone is not
  sufficient. J1 writes it as a Lean definition with a decidable checker.
- Statement selection: the adversary chooses the public statement adaptively
  (one-attempt experiment, statement output by the prover program).
- Trusted preconditions, stated as explicit assumptions, not proved: the
  Solana runtime enforces account ownership and write permissions; the tx1
  checkpoint account is owned by the verifier program and written only by its
  tx1 path after strict parsing; proof bytes are immutable after
  finalisation. Everything after these is in scope.

## Decision 2 — classifier: causal two-stage reduction, not a raw-table adapter

The arbitrary-table quantification of FS2.D2 cannot be met by a classifier
whose words are fixed only causally (`D2TableBoundary.table_flip_cost`).
Decision: **two stages, BCS style.**

1. **Idealised-commitment protocol `prA`** (words are messages): prove
   round-by-round soundness D1/D2/D3 for `prA` with the existence/no-hit
   classifier of `CLASSIFIER.txt` and `maxErr = qcap` (J5). No hash events
   at this stage.
2. **Compiler theorem**: the Merkle-committed protocol reduces to `prA`
   outside the combined collision / missing-preimage events, using the
   causal recovery chain (`CanonicalMerkleRecovery`, `ThreeCommitmentRecovery`,
   `CausalCommitmentStability`) and `D3Outside` (J3, J6).

Knowledge (J7) uses the straight-line extractor reading preimages from the
first-read log, as in BCS; no raw `UnifiedProtocol` classifier adapter is
built. Membership soundness and knowledge soundness stay separate theorems
until J7 joins them.

## Decision 3 — extractor contract

Accepted: an expected-polynomial-time, **Las Vegas** extractor (it verifies
`Rspend` before returning, so wrong outputs are impossible; failure is only
non-termination within budget). Cost model: field operations plus hash-log
lookups, with a stated polynomial bound in the code lengths and the list
size 100. Failure allowance `δE ≤ 2^-120`, charged in the ledger; retries
are allowed and counted. No dense interpolation runs are part of the proof.

## Decision 4 — scope, query accounting, verification order

- Source scope: the verifier program (tx1, tx2, authenticated parser,
  checkpoint write/read, all hash inputs with length bounds) and the Pool
  adapter's binding of the public statement. Settlement logic (lanes,
  nullifier set, custody) is a release gate, not part of the soundness theorem.
- Query accounting: `QV`, the verifier's distinct reads, is proved for **all**
  inputs including rejected ones; `QA` is the adversary's budget and stays
  symbolic. Measured counts (583/452) are evidence only.
- Order: J1 → (J5 ∥ J2) → J3 → J6 → J4 → J7 → J8. Each job gets a
  lead-fixed statement before it starts; the build host runs one Lean job at a
  time through `run2.sh`; one axioms audit and one frozen-manifest replay of
  the whole tree at the end (AGENTS.md). J1's statement is the next lead
  deliverable.
