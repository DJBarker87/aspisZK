# Current native row arithmetic traversal

`Port4C_RowStd.install` makes physical slice/basis reads and pure release
embeddings/traces concrete while retaining the existing named native-to-owned
push boundary. `step` executes the current native row, including repeated
wrapping offsets. `Port4C_RowLoop.from_iterate` transports the COMPLETE
successful owned row traversal to the CURRENT native Range iterator by
symbolic induction. No64-cell normalization or per-row successful push premise
is introduced.

`Port4C_RowMeaning.rows` composes the existing total S7 row proof with that
transport. The current native traversal yields its own PushTrace, updated
phase for all64 rows and exact per-limb sum update. Initial history/phase,
canonical power, canonical basis, size64 and next≤22 are explicit caller
inputs here. Pending proves initial history/phase; full query induction and
basis semantics still need to supply subsequent inputs. Primitive historical
backend certificates are not attributed across source changes by this proof.

Accepted034/041/042, exits0,swap0,standard axioms only. Failed032/038/039 are
excluded elaboration attempts. Exact section6 fields/limits/dependency pins
are in receipts. No full regression or cap increase. Budget42/100 Lean,0/60
Kani at the final row target. No shipped or key changes; no ELF rebuild needed.
