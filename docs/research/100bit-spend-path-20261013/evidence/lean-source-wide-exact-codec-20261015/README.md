# Source WideExact coordinate codec evidence

This bundle preserves all four focused attempts for `R1SourceWideExactCodec`: attempt `source-wide-exact-a` failed on the incorrect `R1UnrolledWideParserRefinement` module prefix; attempts `-b` and `-c` failed during proof elaboration; attempt `-d` is green and is the final source. Every attempt snapshot, receipt, source/target SHA sidecar, output log, and timing log is retained. No compile was rerun during collection.

The final module defines a total coordinate interpretation from the extracted candidate QM31/WideExact records into the retained exact tower, proves agreement for values constructed from strict decoded limbs, and composes the existing successful unrolled parser theorem with the four-WideExact folded leaf codec. This is representation plumbing only; it does not prove source arithmetic refinement, caller correspondence, or protocol/security properties.

The successful compile emitted one harmless unused-simp-argument warning for `residueEquiv_natCast`; the source was retained exactly and no rerun was performed for the warning. Its three public axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

Final attempt `source-wide-exact-d` ran in the pinned NUC workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`, target `R1SourceWideExactCodec`: exit 0, 1.84 seconds, peak RSS 3,808,492 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. `source-manifest.json` records source, import, object, runner, and attempt provenance.
