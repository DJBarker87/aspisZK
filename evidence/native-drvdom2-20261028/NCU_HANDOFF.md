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

# Stage 2: full-outcome model prefix factorization

NCU_PrefixTail.factor (L022) and NCU_WriterPrefix.factor (L031) establish
`tx1 ops D semantic pub proof split hash none = finish ops D pub proof hash
(beforeWriter ops D semantic pub proof split hash)` for arbitrary Ops and
all outer fail/div and protocol Err outcomes. beforeWriter returns the exact
Prepared and post-flush Accumulator at the invocation point. No child success,
canonicality or acceptance premise occurs in this factorization.

NCU_WriterPrefix.Reached is success of this exact prefix. resume proves that
on ANY such call the remaining execution is precisely
`do bytes <- ops.op16 D p a proof pub hash; ok (.Ok bytes)`.
no_later_reject proves a reached call cannot subsequently return protocol Err.
It can fail/diverge inside the writer (outer Result); these calls must not be
identified with NCT's accepted-cut class without writer-success evidence.
This is a mathematical/model control theorem, not native instrumentation or
source-to-ELF refinement. Observer=None is essential and unchanged.

Rejected attempts L004-L021/L023-L030 receive no proof credit. L016/L018/L019
hit the default heartbeat bound, not OOM; the full traversal was split into
head/tail modules, then explicit symbolic bind steps replaced broad traversal.
The remaining head mismatch was generated matcher transparency, resolved by
an explicit kernel-checked `with_unfolding_all exact h` on symbolic terms.
No limit was raised. Tail L022: exit0,2.903512s,RSS5383788KiB,swap0.
Head L031: exit0,3.165962s,RSS5383284KiB,swap0. All four roots standard axioms.
