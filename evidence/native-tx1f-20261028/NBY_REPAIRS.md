# Own script repairs

Setup transport completed but scratch materialization failed before any prover: the root directory was not created before its first symlink. Added explicit mkdir before traversal. No scope launched, no shared infrastructure modified.

The serial runner initially recognized uppercase TIMEOUT but not Kani’s “CBMC timed out”. K015 timed out and its preconfigured K016 control was submitted before review. Neither has credit without passing evidence. Detection now normalizes case and recognizes both spellings; later serial batches stop before a matching shape. This repairs our own wrapper, not shared infrastructure.

Budget guards now count actual terminal invocations (80 Kani, 60 Lean), rather than also limiting numeric attempt IDs. This allows an unlaunched matching control to remain deferred after a timeout while a genuinely smaller replacement uses a new ID. The invocation limits remain unchanged.

After K017 timed out, new row variants hold the hash reply by reference (removing harness-context array copies) and keep inside/outside observations separate. Supplied rows now quantify the actual slice length up to5504 as well as cursor; a fixed96/full-capacity-only slice was a stronger domain than callers establish and is not credited. K017 source snapshot remains immutable; its control stays deferred. Generators retain executed config files and avoid duplicate owner-module declarations.

The broadened timeout detector matched the printed --harness-timeout flag and paused after the successful K025 and K029. Repaired it to match actual “CBMC timed out” / “harness timed out” diagnostics or process exit124/137. Their unchanged exit0 receipts remain passes, awaiting their controls; no positive rerun is needed. The false review/empty cleanup logs are retained.

Final metadata collector had an unescaped empty dict inside its remote f-string, caught as a local SyntaxError before any host call. Escaped it, preserved NBY_FINALIZE_PRECHECK_FAILURE.json and continued metadata collection only; no prover repeated, no shared infrastructure changed.

Final packet export initially treated untouched Rust files outside crates/programs (which were not in its frozen hash map) as new harness files. git apply --check rejected those pre-existing paths. Narrowed export to modified frozen owners, inherited NBV/new NBY harnesses and exact KMX files; kept the rejected check and draft hash, then rechecked the packet locally. No host/prover rerun or source change.
