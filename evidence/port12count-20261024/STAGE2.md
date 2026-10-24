# Concrete owned counts and retained driver boundary

Established (all inputs/H, no acceptance premise):
- Port12COUNT_BatchLeaf.active: one leaf read per actual active key iteration,
  including duplicate-before-compare and rejected duplicates.
- Port12COUNT_BatchTail.terminal: capacity+d-1 reads for the actual terminal
  BatchStep with its checked capacity lookup, capacity guard, padding scan,
  checked used-prefix slice and physical P6. The lookup and <=172 premise are
  proved at every concrete batch0/batch1 tree caller.
- Port12COUNT_BatchLoop.count: actual source fuel loop <=
  capacity+d+2*(n-pos)-1. This is NOT a per-fuel bound: it telescopes the
  actual cursor and distinct-prefix changes. Source continuation proves
  nextPos=pos+1 and nextD=d or wrapping_add(d,1); wrapping never increases by
  more than1. Errors need no successful progress. Fuel exhaustion retains its
  preceding log. No sortedness, canonical field/index values or output count
  is assumed.
- Port12COUNT_BatchTree.batch0/batch1: actual capacities146/146/128 and
  172/172/150, actual10/12 key iterations, tree caps165/165/147 and195/195/173.
- Port12COUNT_Batch.values0/values1: actual short-circuiting3-tree source,
  <=477 and <=563. All base Ops are arbitrary: the physical hash sites are
  explicit Code.read; the other extracted pure callbacks retain fail/div.
- Port12COUNT_Installed.batch0/batch1: the INSTALLED reply-driven op5 Programs,
  including error lowering, <=477 and <=563. No accepted-return assumption.
- Port12COUNT_Installed.owned_calls: four ACTUAL installed call observations
  (batch0,writer,current18,batch1), arbitrary states, total length<=1046.
- checkpointChain_count: concrete owned-call projection with writer-returned
  saved Vec fed to current18 and its returned Prepared fed to batch1; all
  errors short-circuit; log length<=1046. This projection omits delegated
  interleaved calls and is NOT asserted equal to the complete driver.
- Port12COUNT_FirstReads: explicit sufficient total-length metric implies
  <=1046 first reads for the same owned observations/projection. Source log
  length and first-read count remain different metrics. Repeated hash calls
  were counted separately in every total-length proof; no freshness premise.

No prior theorem premise was edited; no before/after weakening is claimed.
New installed theorem statements are unconditional in D/hash/H/proof/Prepared/
folded for which=0 and which=1. The only native capacity-table premises live
in local generic tree/loop helpers and are discharged by six actual source
lookups. D's arbitrary failure/divergence policy is retained throughout.

The audit calculation1040 is now a physical source theorem for the sum of
both installed batches (477+563); owned checkpoints give1046. No theorem
claims that arbitrary which values use the batch0/batch1 profile; source
splitting for nonzero which and wrapping slots must not be silently treated
as batch1. Actual driver literals are0 and1.

## Exact remaining composition

The complete Port1_Driver.stages still contains delegated op3/op4/op7/op6/
op17 and other rest calls, interleaved with owned calls and determining their
arguments. A concrete implementation must prove the ACTUALLY executed
remaining-call total<=115, on ALL rejection/outerfail/div prefixes as well as
successes. The source control-flow partition must show at most one batch0,
one writer, one current18 and one batch1 in their actual order, retaining the
arguments returned by prior calls. Then actual ordered-log composition uses
477+3+3+563+115=1161. No whole-count/equivalence hypothesis is substituted
for that producer. Unrestricted rest can issue arbitrarily many queries, so
this job does not claim full source1161, classifier/no-hit, all-H sampler
containment, terminal security or either deployed target. Session A's pending
op3/op4/op7 producer request was not duplicated, and no Session A worktree or
candidate was read or changed.

The target stays (Q+34)*B+kappa(Q+1161)+2^-126+2^-454, B=15/2^109.
No transcript credits, collision charges, conditioning or grinding were added.

## Failures retained

001/002: definitional simplification and quoted `at` field syntax.
003: local read32 specification attribute needed at the physical node proof.
005/006: Code.bind unfolding and pure continuation simplification.
007: pre-Lean missing Rows object; conservative reservation retained.
009: zero-height definitional simplification/scalar theorem name.
013-016: pure lambda inference, prefix slice unfolding, tactic syntax, and
actual table equation available only after the nested lift had reduced.
018: pure final continuation and projection of progress pair.
020-022: tuple-pattern continuation and explicit tiny source slot parameters.
025: output type and polymorphic Implementation let annotation.
027: missing namespace openings for the first-read metric.
All failed sources/full logs remain. No resource failure, raised cap,
heartbeat/recursion override, unchanged failed source rerun, full manifest,
runtime suite, SBF/ELF build, Kani or Rust gate occurred.
