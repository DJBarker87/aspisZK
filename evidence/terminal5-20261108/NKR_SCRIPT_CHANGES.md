# Own input-client repairs

Inherited NKI client renamed privately to NKR; budget140Lean/70Kani/0extraction,own workspace/target, same admission+caps+transport+disk policy. NKI seed first,NKN second, hashes/bytes checked before each scope. NKN inherited dependency paths added after L001; no infrastructure change.

Native own-input hash changes are staged only by committed exact delta patches with git apply --check, then all frozen/source/graph/lock checks remain. K003 validation stopped before Kani after missing upload of first delta; K011 corrected the required input manifest. Original K003 retained.

Required validation-input existence is now asserted (previous inherited code silently omitted absent entries). Queue scheduling now checks every direct NKR import plus explicit prerequisites against current source-hash-matched passing receipts, preventing missing-object prelaunch mistakes such as L038/L063/L076. No test or source check weakened.

All scopes use existing unchanged S2W_run_host.py and existing reservation script; no launcher/shim/monitor infrastructure modified.

Final-gate repairs: NKR_ProofDriver source/binary reused byte-identically from NKI after hash checks; own NKI runtime aliases are byte-compared to NKR manifests. L183 initially stopped before submission because the failed combined import produced no object (no charged scope). Diagnostic audit pinning excludes the absent object and imports its exact61 own modules plus both baseline combined modules directly. Validation of every existing object and raw axiom criteria is unchanged; this is explicitly incomplete combined-gate evidence. A local active-client guard blocked a premature queue invocation before submission; retained transport logs, no duplicate scope.

Permanent generator repair (not replayed): NKR_build_gate.py now emits source-level check/axioms commands only for public names, retaining every private root unmodified in the full raw roots/groups and private-import module inventory. A source comment names each retained private root. This avoids rendering internal Names as inaccessible public syntax without dropping private dependency validation. Python syntax checked; neither generator nor a third combined build was run. The committed NKR_COMBINED_IMPORT remains the exact second failed source. NKR_GATE_REPAIR_PROPOSAL.patch shows its proposed future command delta.

Final hygiene correction: initial local text check overmatched every set_option, including autoImplicit false. Re-read r1p-common rule3: only new maxRecDepth/maxHeartbeats options are forbidden. Allowed the stricter autoImplicit false directive explicitly; all other option directives and forbidden proof forms remain rejected. No source proof was changed and no formal scope was launched.

Raw admission/launcher logs retain exact captured whitespace and EOF bytes. Scoped .gitattributes disables cosmetic whitespace diagnostics only for those two raw log patterns; Lean, Rust patches, scripts, receipts and other documents retain normal whitespace checks. No evidence log is normalized or rewritten.
