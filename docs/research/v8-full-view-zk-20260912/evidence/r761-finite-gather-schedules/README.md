# R748 finite gather schedules

This is a source-only generator for the index schedules and generic gather identities used by the 343 `needed_pointWeight_indices` in the pinned R748 plan. It does not evaluate field values, perform elimination, prove rank, or establish source execution.

Run `python3 .r21-scratch/r748-gather-schedule-generator/generate_schedules.py --check` to verify the pinned plan, `IndexSchedule`, R742 and existing R748 schedule inputs plus every generated Lean chunk. The plan pin is `55f19bf194589ef1229ae6d96ce0d7ef16b1b8d3466b40d00cc0e9fa4b906dd4`. The generator uses ten fuel steps as `IndexSchedule.indexLoop` specifies, retains only needed rows, and emits at most 32 theorem declarations per file. Each schedule, gather and nested-gather lemma includes a `#print axioms` command.

The densest requested schedule is row 255, with nine edges. Its proof and required child schedules were compiled once in `PrototypeDensest255.lean`; generated chunks import and reuse those names. The prototype compiled with exit 0, wall time 1.63 seconds, peak RSS 3,304,528 KiB, and swap 0. Its nineteen printed reports all list `[propext]`. The earlier failed proof-script attempt is preserved in `.r21-scratch/aspis-focus-1791145019543898000.log` and its receipt.

All 21 generated chunks have since compiled successfully in the pinned cache: eight loop chunks, eight gather-expansion chunks, and five nested-gather chunks. The initial prototype and initial Nested00 proof-script failures remain separately preserved in `compile-status.json` and their full `.log` and `.receipt.json` files. `compile-status.json` records every successful target, source checksum, source revision, exit, wall time, peak RSS, swap, complete axiom-report count, and remote OLean hashes.

Derived coverage: 343 pointWeight indices, 230 outer schedule rows, 153 nested outer rows, 250 distinct schedule rows through row 510, and at most 9 edges per schedule. The generated outputs total 229 loop, 231 gather, and 150 nested-gather lemmas. Existing R748 lemmas and the green prototype are reused rather than regenerated.

The proved boundary is finite schedule computation and generic sourceGather algebra for these planned indices. No point evaluations, verifier execution, field-specific statement, rank, privacy, or security conclusion is included.
