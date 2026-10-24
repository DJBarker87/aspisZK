# Preserved failures

- lean-001: diagnostic attempted `reprStr ConstantInfo`, which has no Repr instance. No theorem checked. Replacement prints the type/value pair; lean-002 passed.
- lean-003: diagnostic loaded the entire root Environment through interpreted importModules; interpreter memory exception, exit 134, 4.615s, 6,142,788 KiB RSS, zero swaps. No theorem checked. Not rerun with larger limits. Replacement reads module data sequentially and stores only name/dependency edges; no Environment/extension construction. Original source and logs retained.

- lean-004: first raw traversal still retained compacted module data; interpreter memory exception, exit134, 4.310s, 4,507,652KiB, swaps0. Replaced by per-module region release after cloning dependency strings; lean-007 succeeded at1,603,632KiB. No limit increase.
- lean-006: region-releasing diagnostic had an ambiguous numeric accumulator and redundant unsafe/partial modifiers; no evaluation. lean-007 fixes both.
- lean-009/010: raw snapshot record-update layout parse errors, no evaluation. Replacement011/012 only reformats fields.
- Initial007/008 diagnostic omitted theorem/opaque bodies because ConstantInfo.value? defaults allowOpaque=false. They are explicitly superseded for proof reachability by011/012, which also include mutual/recursor rules and correct the source seed.
- lean-015/016: both charged pre-Lean guards. Exact process matching replaces a regex that matched another worker command; the repeat guard now includes launcher hash to identify the tooling correction. No Lean ran; no RSS/wall/swap is invented.

- lean-017: unsupported liftIO name in run_elab; automatic IO lifting replaces it. lean-018 succeeds.
- lean-019: exit0 but repeated AsyncConsts normalized-private-name PANIC diagnostics; NOT accepted. Kernel addDeclCore had been called through the elaborator wrapper, which attempts to put private declarations from many original modules into one normalized-name map. Replacement restores stock Lean.Replay's Kernel.Environment state and Environment.ofKernelEnv return. This preserves original private names without renaming and avoids elaborator name-map collisions; every declaration is still kernel checked. Rebuild helper and stages; no cap change. Launcher now rejects PANIC even on exit0.

- lean-021: stock kernel replay succeeds, but newly added declarations live in the kernel map's second stage and are not available to same-file elaborator #print commands after Environment.ofKernelEnv. No field mutation or unchecked insertion is used. Replacement022 exports the already kernel-checked object, and the next normal import exposes declarations; the single focused audit runs after normal imports.
- lean-024: stages theorem was not among snapshot seeds; its existing frozen driver object was retained in Port17 receipt018. Supplemental transport pins that exact object and source hash (including stages._proof_*), without source editing. Replacement025 succeeds.
- lean-027: audit counter's implicit type was inferred as MessageData; explicit Nat annotation fixes it. Replacement028 passes full identity, types, hidden structure and axioms audit.

- Final source-only receipt checker initially selected a helper receipt by filesystem iteration order. Replaced by the greatest attempt identifier; current-source hashes and accepted dependency objects pass. No Lean execution or new attempt charge.
