# Candidate Wide parser contracts

Focused NUC evidence for `R1CandidateWideParserContracts`. Attempts a–e are preserved proof failures; attempt f compiled successfully under the recorded 4G/6G/zero-swap cgroup. The final module proves total `Result.ok` behavior for arbitrary slices, exact strict-limb witnesses for successful fixed-array parses, and canonicality of both QM31 halves after successful parsing.

The final `#print axioms` output for all three public theorems was exactly `propext`, `Classical.choice`, and `Quot.sound`. This is a contract for the retained candidate parser model; it makes no runtime-source refinement or adoption claim. The source snapshot and receipts are hash-matched in `source-manifest.json`.
