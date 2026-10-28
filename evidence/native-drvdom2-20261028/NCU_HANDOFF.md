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

# Stage 3: all-prefix domain and conditional leaf

NCU_DriverDomain.prefix_of_reached derives split10 and Prefix from the SAME
beforeWriter execution under the two unchanged offset equations. Prefix is
NCL's complete cut inventory EXCEPT checkpoint success. It contains shape,
scan, zero, preparation, root bounds/copy, initial, batch, geometry, pending,
query and flush calls. It imposes no writer-return or final acceptance premise.
Thus every reached writer is in this pre-writer accepted-prefix class, but
failed/diverging writers are not in NCL.Cuts (which additionally asks success).
accepted_when_writer_returns proves the missing acceptance implication exactly
when the actual op16 returns, without postulating a second accepted execution.

control composes existing constructor, loop_raw, flush contents/canonicality
results on this Prefix and derives 64 weights, next10 and all flushed weight
canonicality. It does not require writer success. domain transports these to
the leaf's raw writer fields. This extends NCT's accepted-call conclusions to
all release model writer prefixes, including those whose writer fails/diverges.

After: NCU_DriverDomain.leaf has a Prefix of currentInstalled c/currentDigest c
and the three SAME pointwise field gates (S2, 22 query bounds, nine nonweight
canonical groups). It has NO WriterDomain, DriverEstablishedDomain, writer
success or accepted-run premise. Under the unchanged leaf's same-body local
append correctness, chronological three digest calls and oracle interpretation,
it proves output length1768, exact returned bytes, chronological writer read
log and the encoding of the SAME pm/am. Unlike NCT's accepted leaf it does not
claim equality to an accepted saved Vec: that carrier does not exist for a
failed writer. No change to proof/public/hash/Prepared/Accumulator carriers.

**Target not yet established unconditionally at model level.** S2, all query
bounds and gamma/kappa/alpha/rho/semanticAlpha/coordinates/claim/rhs/power are
still explicit obligations, not discharged by a new structure. No arithmetic
primitive law was fabricated. The next deliverable remains an actual-instance
same-prefix preparation/query arithmetic theorem. The stage1 statement audit
identifies why the listed model lane results cannot simply instantiate free
Configuration.boundaries and query operations. No impossibility theorem or
counterexample to full model closure was proved; this is an exact remaining
obligation, not a claim that further Lean work cannot close it.

L032-L034 are rejected record-construction drafts; L038 is a rejected notation
capture draft. L035-L037 pass the successive prefix/control/domain targets.
L039 is the complete conditional leaf: exit0,2.948817s,RSS5410044KiB,swap0,
standard axioms for all five module roots. Predecessor generic lemmas were
imported; new proofs invert/factor the driver and compose their results.
