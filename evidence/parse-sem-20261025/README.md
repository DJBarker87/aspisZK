# Parser/semantic source refinement

Branch codex/cx-parse-sem-20261025; modules PSem_ only.
Budget: 100 Lean attempts including dependencies, 40 Kani runs.
Only new proof modules and this evidence directory may change.
All jobs use existing host launchers, -M7000, MemoryHigh6G/MemoryMax8G/Swap0/Tasks64.
No shipped source change, artifact rebuild, package replay, or new trust item.

Read: root AGENTS.md Security and proof discipline, common/local rules,
S2 ownership/plan/diagnosis/interface, adopted C3-BIN route B, SInt2,
Op3I, Op4P and Tx1Q handoffs. Historical paths resolve in the research tree.

Target: remove parseReached and LiteralMatchingData.read from the SAME
accepted TX1 endpoint. Conditional wrappers do not earn removal credit.
Source chain: candidate::prepare -> compact::expand_semantic ->
r1_semantic::verify_observed -> Prefix::parse -> semantic transcript;
Prepared::new supplies opening rows 27..32. The full transcript must include
semantic and opening absorbs in order, with the same challenge carriers.

Initial audit: frozen rowShape agrees with shipped row_shape on rows0..26.
Source compact expansion copies framing without validation; canonicality and
framing are checked subsequently by Prefix::parse. Therefore expansion success
alone is insufficient to conclude semanticRows27. Existing Claims success does
not establish Aligned or the complete matching-data read.

No premise removed at stage 1. Source/artifact pins inherited unchanged;
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
These are inherited pins, not reproduced builds. No release claim.

Final: budget100/100 exhausted; semanticRows27 subobligation checked on the
SAME accepted run. Both complete top gates remain open. See HANDOFF.md for
full premise audit, non-vacuity limitations, exact metrics and next work.
