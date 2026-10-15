# Unrolled Wide parser refinement

This bundle records all four focused attempts for module `UnrolledWideParserRefinement`; the final `d` source is green and matches the current Lean source byte-for-byte. It imports the three pinned modules listed in `source-manifest.json`: `UnrolledWideByteReads`, `R1UnrolledWideLimbChecks`, and `R1CandidateWideParserContracts`. Those predecessor bundles retain their own import closures and attempts.

Final `d`: exit 0, 1.88s, 3,797,088 KiB peak RSS, zero swap, cgroup 4G/6G/0. All six public theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The archive stores the final target object and a separate archive stores the three direct import objects; no loose `.olean` files are retained.

This is a Lean refinement result for the selected retained generated parser. It makes no runtime adoption claim.
