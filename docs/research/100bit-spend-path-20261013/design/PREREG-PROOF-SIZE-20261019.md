# Pre-registration: proof-size feasibility test (2026-10-19)

Written by the lead before any work starts. Criteria may not change after
results are seen. Input: `PROOF-SIZE-PROPOSAL-20261019.md`. Motivation
(user): the number of proof-upload transactions is a key user-interface
cost; the proof is uploaded in about 1 KB pieces.

## Target

A candidate proof format for the R1 S2 salted proof: compact QM31 encoding
plus binary Merkle trees with one multiproof per tree per transaction batch,
as in the proposal. The candidate is built as a separate variant beside the
shipped verifier (the shipped path and its ELF stay byte-identical). Base:
`research` at the job's base commit.

## Measurements (fixed)

1. **Size.** Exact stored proof bytes for each of the six saved fixtures'
   witnesses re-proved in the candidate format, and a worst-case bound over
   all query sets with a counting argument (occupied ancestors per level),
   since the parser and checkpoint need a bounded length. Also reported for
   the two weaker layouts (compact only; eight-way multiproofs plus compact)
   as calculations checked by an encoder, for the record.
2. **Compute.** Stage-1 transaction CU and Pool settlement CU (with nested
   stage 2) for the candidate, on the six fixtures' witnesses, using the
   cu-bound2/pool-b1 harness, with the checkpoint authenticating the compact
   stored bytes. Compared per fixture with the B1 figures
   (`LEAD-REVIEW-POOL-B1-20261019.md`: stage 1 ≤ 1,199,687, settlement ≤
   1,170,523).
3. **Uploads.** The number of upload transactions for the candidate proof
   at the current upload instruction size, next to the current count.
4. **Parameters.** 22 queries, two folds, final length 64, the salt policy,
   and every genuinely wide WideExact value unchanged. Confirmed by diff.
5. **Teeth.** The candidate verifier rejects: a wrong sibling hash, a
   missing or extra multiproof node, a duplicated or misordered leaf index,
   a non-zero byte where a compact field's zero half is implied, and a
   checkpoint over the expanded rather than the compact bytes.
6. **Obligations.** An inventory of the Lean modules and theorems the
   format change would revisit (commitment binding, multiproof verification,
   extractor word recovery, serialization, oracle-read counts, simulator
   layout), by name, with a size estimate each.

## Acceptance

- VIABLE: worst-case stored bytes ≤ 60,000; measured stage-1 CU and
  settlement CU on every fixture not above the B1 figure for that fixture;
  parameters unchanged (4); all teeth reject (5); inventory written (6).
- NOT VIABLE: the size bound exceeds 60,000, or any fixture's CU exceeds its
  B1 figure. Report which, and by how much.
- INCOMPLETE: a measurement could not be made; say which and why.

A VIABLE result is a measurement of a prototype, not a security claim. The
worst-case CU bound (`PREREG-CU-UPPER-BOUND-2-20261019.md`) must be re-run on
the candidate before any 1.3M claim, and the obligations in (6) must close
before any soundness or privacy claim covers it.
