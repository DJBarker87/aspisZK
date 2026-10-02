# R340 selected batch-output raw staging

Uncompiled mechanical staging from the frozen R292 generated function input. `provenance/R292Funs.input.lean` is an exact byte copy; the builder checks it and the original saved input against the authorized SHA-256 before extracting any text. `selected-source-fragments.txt` records the original declaration/body text and source line boundaries. `raw-binding-audit.json` records fragment hashes, existing namespace bindings, caller guard/traversal boundaries, and unresolved compiler/Std dependencies.

The new Lean file copies both `B.Insts.CoreCloneClone` declarations exactly and wraps only the two authorized contiguous body fragments. The first fragment is original lines 569–586 and runs the reverse loop over `xs` with loop2 before writing element zero. The second is lines 587–604 and does the corresponding work over `ys` with loop3. Both wrappers return the resulting vector in `ok`; the original full callback terminator and surrounding guards are outside these selected fragments.

The source text inside the copied clone declarations and wrapper operation fragments is unchanged. Imports and wrapper signatures are staging scaffolding; no helper body is invented or replaced. `#print axioms` commands are included for both clone declarations and both wrappers, but no Lean command was run and no output is claimed.
