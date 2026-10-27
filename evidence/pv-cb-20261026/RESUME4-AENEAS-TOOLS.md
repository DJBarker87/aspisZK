# Aeneas tool identity and restoration limitation

Earlier successful extractions in this branch did not all use the same binary.
For example, aeneas-source-op107-resume3-001/target.json records
`/home/dombarker/project-offloads/codex-pv-cb3-20261026/pinned-tools/aeneas`.
That exact path is now absent. Earlier direct op223 extraction used the also
now-absent v7-tag73-challenge-qm31-source-20260825-work/toolchain/output binary.

The surviving own pinned Aeneas is49481680bytes, SHA256
`562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19`.
Its current op223 attempts stop at the ProverRwRngExtractor006 escaping-reference
preflight. These are tool-qualified failures, not evidence that every earlier
accepted source law used this guard or that all tool variants fail identically.

No guard is disabled, no backend is repaired/rebuilt, no shared tool is edited,
and no unvalidated translator replaces it. Continue Lean/P6 while recording the
missing earlier accepted extraction tool as a restoration limitation.
