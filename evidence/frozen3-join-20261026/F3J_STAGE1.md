# Stage 1 — same-cut input constructor

F3J_NativeInput.from_cut constructs an F3_Model.Input on the supplied SAME f,s
SourceCuts, native semantic_public selection and successful TX1 Run. Physical
bytes are exactly bytesOf f.pub.val, stored exactly bytesOf f.proof.val. Semantic
public bytes are the successful source public_bytes output and actually parse.
All33 erased proof messages use the source parsed semanticRows and physical
suffix rowBytes; the initial root comes from the same proof range16..48.
F3J_InputRows.valid checks the literal constructor schedule. Auxiliary word
metadata remains an explicit parameter; no source recovered-word claim yet.

This discharges the local constructor gap after the existing derived TX1 Run
and selected-cut predecessor, not the native accepted-pair complete join.
No sampler-log equality, model acceptance, Prepared or accumulator binding is
assumed or concluded. Existing source/SDK/history/primitives boundaries remain.

5 actual Lean invocations, 3 passes and 2 excluded elaboration/import failures.
Before attempt001 the launcher reported missing PAln_RowBounds without invoking
Lean. Reused the existing PAln workspace and PSem objects through LEAN_PATH,
leaving all foreign-prefix files/objects unchanged. No launcher modification.
Attempts001,003,005 compile final modules; axioms only propext/Classical.choice/
Quot.sound. Each receipt preserves target, command, SHA, dependency fingerprint,
revision, exit/wall/RSS/swap, limits, full stdout and axioms. No timeout or OOM.
