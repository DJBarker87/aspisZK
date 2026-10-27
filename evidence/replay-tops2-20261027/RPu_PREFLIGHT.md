# Preflight corrections (no Lean invocations)

Initial graph discovery used recursive directory traversal; it was stopped
locally before any host proof invocation and replaced by an rg file inventory.
The first static graph pass found a diagnostic duplicate prepared-channel-loop
source and an Aeneas.Std.WP import. Source selection now follows the coherent
workspace: diagnostics are out of source resolution, and WP is an already pinned
Aeneas library. No alternate proved source or host object was substituted.

Before the first compiler invocation the job-input path was checked to include
RPt_overlay between RPu_overlay and RPz8_overlay. 2500 retained paths rehashed
without mismatch. These checks consume no Lean attempt budget.

A source-statement byte check subsequently found only an extra trailing blank
line in FJu_after.lean.txt. The raw equality is recorded false and the normalized
source equality true. Full fresh kernel statements and independent byte comparisons
remain separate gates. Recount script recomputes all four ledgers from atomic rows.

Before reaching any dotted module, 32 future module aliases were flattened
to unique RPu identifiers to match the unchanged launcher output layout.
All already compiled snapshot hashes were checked unchanged; logical declarations
and source bodies are unchanged. RPu_module-name-check.json retains the list.
