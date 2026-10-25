# Stage 3: source preparation and root provenance

Checked source facts, not new hypotheses:

- SdkD_PrepareCut.first obtains the actual preparation/zero/scratch return,
  physical7751..7783 folded-root read/copy, and successful batch0 from the
  SAME first SourceCut. Constants derive from the exact installed dictionary.
- SdkD_PhysicalRoots.prepared applies the coherent SInt2/native preparation
  proof to that actual return: both roots are raw proof slices16..48 and63..95.
- SdkD_ParserRoot/ParserRows/SliceAlgebra invert only the first three symbolic
  parser rows and identify model C2 root bytes at63..95. No whole recurrence
  normalization is used in the final proofs.
- SdkD_RootBinding derives both model root equations from those bytes and the
  actual stored parser. SdkD_NodeViews computes all physical node slices.
- SdkD_QueryBinding derives exact batch query-map equality from the already
  permitted named SessionAPrepare. The modulo lowering is not assumed anew.
- SdkD_FirstPaths.indexed supplies every indexed batch0 path under the actual
  partial native syscall, without separate prepared-root/node-view premises.
  Actual preparation/copy/batch returns and parser binding stay explicit in
  this LOCAL helper; the source-cut predecessor derives the former calls.
- SdkD_BatchLoopFixed/BatchFixed prove the batch syntax independent of the
  phantom native digest dictionary by structural induction. Thus the syntax
  can be chosen before H. This does not instantiate the whole SDK experiment.

No additional top-level premise-removal credit: the full accepted theorem is
still the stage2 result, and authenticated_S1/global commitment-frame/query
budget are still open. The source-to-model root sub-obligations are now checked.
The exact replay collision term remains6*(Q+1040)^2/256^32, not a premise.

49 Lean attempts used,0 Kani.038 was REVIEW-STOPPED after26s, observed scope
peak892.3MiB, well below the cap. It attempted definitional equality of the
whole source batch and was replaced, never rerun unchanged, by039 structural
loop/tree induction and043 values composition (both green,about1.9s).
The stop killed the scope's time/receipt parent too: no completed time metrics
exist. stopped.json explicitly records those missing fields and partial logs;
no proof credit or invented exit/RSS/swap number. All other attempts have full
standard runner receipts, including failures and exact source snapshots.

049: SdkD_FirstPaths.lean,exit0,1.985383297s,5198360KiB RSS,swap0;
standard three axioms. All successful new top theorems printed standard axioms
only. Caps6G/8G/Swap0/64,-M7000;no cap/option increase, package replay,
shipped/cfg(kani)/ELF/key/other-worker edit. Full release correspondence and
joint accepted-SDK non-vacuity are not claimed.
