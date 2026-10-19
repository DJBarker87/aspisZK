# GS polynomial to executable root-recovery state

The executable coefficient constructor gsRows stores CompPoly coefficient Q[i,j] at runtime rows[i][j]. CompPoly presents the polynomial outer-Y first; RR rows are inner-X first. The bridge proves that this transpose/zero-fill representation has exactly Q.toPoly as its RawState model.

For Q.natWeightedDegree 1 d <= D and D < d*(maxY+1), gsState_contract proves three facts together: exact original-polynomial model equality; degree <= maxY for every stored row used by root recovery; and a nonzero model whenever Q is nonzero. These are precisely the raw-state hypotheses consumed by RRConcreteRawRecovery and the initial-message composition. For the selected initial/final parameters the window inequalities are 114689 < 1024*113 and 28673 < 255*113; this packet retains them as explicit generic premises rather than claiming an instantiated backend caller.

Only V6 plus ConstructorContractV1 form the active closure. V4 declares overlapping constants and is a superseded diagnostic, not a dependency; do not jointly import V4 and V6. Exact focused Lean4.32 sources, objects/imports, commands, source revisions, status, time, RSS, zero process swap and standard-only printed axioms are retained. No full replay or dense elimination was run.

V7 stopped at its aggregate4GiB guard because it overlapped a separately running root target. Its empty diagnostic log and stop receipt are retained. The replacement separates the new contract into a small consumer importing accepted V6; this changed source organization passed at about2.12GB. No unchanged memory-failed target was rerun at a larger cap.

Still open: actual backend witness construction and parameter instantiation, agreement-to-root forcing, complete caller integration and extractor costs, bits-to-field sampling, protocol/source/runtime/ROM composition, full privacy and two-transaction release gates. This coefficient/refinement bridge is not a full100-bit spend proof.
