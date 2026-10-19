# Lead review: J1.R13 arithmetic savings (G_R1.1), 2026-10-19

Reviewed: branch `codex/r1-cu-savings-20261019` at 925dc4b95, merged into
`research` by its session as 7133365cc. Report:
`evidence/cu-savings-20261019/FINAL-REPORT.md`, `FINAL-RESULT.json`.

## Verdict

**G_R1.1 is met on the six saved fixtures, by measurement.** Worst stage 1 is
1,199,687 CU and worst Pool settlement 1,188,496 CU, against the 1.3M target
of D68.1 (about 100k headroom per transaction) and under the worker's stricter
1.2M line. The split between the transactions did not move; the savings are
arithmetic, as the user decided. The lead spot-checked one raw run log
(candidate14 transfer-1023: "1171579 CU", matching the table).

## What this does and does not establish

1. **Measured, not bounded.** These are six fixtures (transfer/withdrawal at
   13, 255, 1023). Stage 1 varies by under 1,500 CU across them, which suggests
   little data dependence, but no worst-case input argument is given. The
   G_R1 covering argument still has to say why no admitted input costs more.
2. **The shipped verifier is no longer the proved one until re-pinned.** Ten
   kept candidates change verifier Rust (gamma powers, delayed dot reduction,
   private dot operands, rho residues, factored S2 Libra row, …). Each
   candidate's `declaration-repin-inventory.json` lists the changed owners and
   the equivalence obligations. Until those re-pins are proved, the soundness
   results cover the pre-optimisation verifier, not the 1.19M one. The session
   is already committing these proofs on `research` (efa2ddcec, 260755780 and
   others); each needs lead review before release language uses the new
   numbers.
3. **Gates.** Every candidate passed codec 1,233, the ordered 583-call trace,
   checkpoint23, injections, SBF build, strict stack audit and the six-fixture
   replays. Four candidates (8, 9, 11, 13) regressed and were reverted with
   evidence kept. The readonly-metadata runtime check (13 mutations rejected,
   two controls pass) backs the `R16ReadonlyMetadataProjection` premise only.
4. **Hygiene.** The c16 `AspisR1PublicPreparation.{Funs,Types}` (Funs
   `e98bb123…`) is promoted into the non-evidence Lean root, as D68.3 ruled.
   Import-only R1 forwarders for SpendRelation, SpendAppendBinding and
   TraceAppend resolve the X/R1X double imports; the five-root manifest check
   reports 718 modules with no conflicts or cycles. This unblocks privacy T4.
   No compile was run on it.
5. **Repository.** Compressed run logs (`*.log.gz`) and two Lean object
   tarballs were committed. This is against the evidence rule (JSON/MD/log
   text only, SHA + size for binaries); accepted once, not to be repeated.

## Next

- Lead review of each optimisation re-pin as it lands.
- A worst-case covering note for stage 1 and settlement CU (what inputs could
  cost more than the fixtures, and by how much).
- Privacy side: the retry-loop/simulator worker must rebase onto the
  optimised verifier and rerun its verifier-acceptance tests.
