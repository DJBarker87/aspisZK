# S2 parser reuse handoff

User direction, 2026-10-21: the parser/multiproof results merged at e5a601bea are available to S2 stage-1 buffer work. Reuse them rather than rebuilding parsing. Neither cone is closed. The narrower lead continuation owns only the pending multiproof sort/insert step and stepwise Kani checks for shipped batch_tree/verify_in_place; those should not be duplicated here.

The reusable parser interfaces on research are:

- `lean/MultiproofConeStrictScan.lean`, `AspisR1.MultiproofConeStrictScan.scan_total`: the complete owned strict scanner equals the frozen canonical model on each 57,607-byte input.
- `lean/MultiproofConeExpansion.lean`, `expand_total`, and `lean/MultiproofConeFrameModel.lean`, `header_model_total`: total compact expansion and exact frame checks under the stated independent bounds.
- `lean/MultiproofConeParserTotal.lean`, `rows_join`, `parse_total`, `accepted_parse`: the complete owned parser's Option/semantic result and accepted wire/semantic identification.
- `evidence/multiproof-cone-20261021/STATUS.md` and its source/command/receipt pins; `design/CONE-AUDIT-20261021.md` records the remaining source joins.

S2 still needs to install the owned parser/control facts at the actual production buffer/caller boundary and connect the exact stored bytes, accepted decoder and runtime carrier. These local/reference results do not by themselves identify parseReached or construct AcceptedRunJoin. Do not add a premise that merely assumes the missing source equality and report it closed.

S4 has already reused the canonical/endian owner: `evidence/s4-canonical-head-inputs-root-v1-20261021/` proves all104 actual head scalar decoder acceptances from the exact608-byte payload's canonical predicate. Its remaining opening/stored-prefix identity can share S2's byte-carrier work. S4's twelve QM tail acceptances and Rust Std boundaries remain separate.

This handoff does not edit the central cone table; each job retains ownership of its own rows to avoid repeating the previous merge conflicts.
