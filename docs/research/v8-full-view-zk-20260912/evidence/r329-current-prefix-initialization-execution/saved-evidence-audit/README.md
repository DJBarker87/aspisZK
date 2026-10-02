# R328/R329 saved-evidence audit

Read-only verification of the two promoted evidence bundles. No Lean command was run and no tracked file was changed.

Both bundles pass: every listed checksum matches; each target is byte-identical to its saved source copy and matches the manifest SHA; the checkout revision matches the recorded revision; and the successful logs agree with exit status, GNU-time wall time, peak child RSS, and zero swaps. Both runner copies specify 5G/7G/0-swap/128-task scopes and Lean `-j1 -M4500`. The complete axiom files match the logs after whitespace normalization. R328 has one report and R329 has two; all reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

R328 stages the exact R292 source lines 527–542 with zero body replacements inside a proof harness. Its nested raw-adapter audit records that it was historically uncompiled; the parent bundle manifest and successful log are the authoritative compile evidence. The fragment begins after the full batch validations and is not a standalone Rust root.

R329 states the empty-fragment `arrayOutOfBounds` result and a nonempty products theorem whose explicit read condition supplies encoded source words. It derives capacity from the valid Slice bound; zero products are not excluded. Full batch guards, the second vector, inverse, caller/source-library correspondence, and security remain open.

Machine-readable checks: `audit.json`.
