# Own script repairs

Setup transport completed but scratch materialization failed before any prover: the root directory was not created before its first symlink. Added explicit mkdir before traversal. No scope launched, no shared infrastructure modified.

The serial runner initially recognized uppercase TIMEOUT but not Kani’s “CBMC timed out”. K015 timed out and its preconfigured K016 control was submitted before review. Neither has credit without passing evidence. Detection now normalizes case and recognizes both spellings; later serial batches stop before a matching shape. This repairs our own wrapper, not shared infrastructure.

Budget guards now count actual terminal invocations (80 Kani, 60 Lean), rather than also limiting numeric attempt IDs. This allows an unlaunched matching control to remain deferred after a timeout while a genuinely smaller replacement uses a new ID. The invocation limits remain unchanged.
