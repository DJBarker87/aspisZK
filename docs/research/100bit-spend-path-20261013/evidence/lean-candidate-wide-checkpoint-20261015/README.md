# Candidate Wide parser frozen checkpoint

The checkpoint imports six modules in the candidate WideExact parser batch and audits their 19 public items. It compiled once as `R1CandidateWideParserCheckpoint` at the recorded 4G/6G/zero-swap cgroup. All theorem reports list only `propext`, `Classical.choice`, and `Quot.sound`; the WideExact structure itself reports no axioms.

The six direct source/object inputs are hash-pinned in `source-manifest.json`; each predecessor evidence bundle retains its complete attempts, including failures, and is linked there. The final object archive contains the six inputs plus this checkpoint. This is a Lean checkpoint only and makes no runtime adoption or source-refinement claim.
