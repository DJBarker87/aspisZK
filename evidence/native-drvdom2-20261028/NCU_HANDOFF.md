# Stage 1: statement audit

Target not yet established. New Lean modules only; predecessors unchanged.
Before: NCT_DriverDomain.native_result takes one accepted NCL cut and three
pointwise gates: S2, 22 query bounds, nine NonWeightCanonical groups.
NCT.Reached is accepted-cut reachability, not every reached writer call.

NCU_L003 co-imports NCT, NBR/NCA/NCH and NBO/NBW/NBZ/NCG audit roots.
The printed statements distinguish actual Configuration primitives from the
concrete arithmetic functions proved in those lanes. In particular:
- Configuration.boundaries.circle remains a free function into an unrefined
  SecureCirclePoint carrier, and std remains free.
- NBO_WriterEntry.same_writer assumes NBA_NBC producer laws, NBC_Bounds,
  Lower and NBC_Bindings, on a different VTop installation.
- NBZ_Folds.circle_total proves its own explicit arithmetic function; it does
  not assert c.query.op16/op17 equal that function.
- NBR_PrepareTotal and NCA_ReturnedScanInputs construct a cohort result with
  explicit producer observations/total-digest requirements; their statements
  are not unconditional field invariants of arbitrary currentInstalled c.
These are missing concrete model instantiations, not cryptographic assumptions.
No whole-component closure follows from the co-import.

Validation: L001/L002 are rejected audit name-resolution drafts, zero credit.
L003 exit0, 2.233449s, peakRSS5424428KiB, swaps0; standard axioms only for the
four inspected roots. Exact source/dependency hashes/revision/limits and full
statements are in NCU_ATTEMPTS.jsonl and NCU_L003/. Backend scripts copied
byte-identically from existing S2W; NCT persistent cache reused and retained.
Next: prove exact pre-writer factorization and distinguish outer writer
failure/divergence from protocol rejection after a reached call.
