# NLF failed steps

Target not yet established. L002 failed on record eta and an unavailable erase
lemma; L003 replaces it with structural cases and List induction. L004 failed
on nested-match layout, fixed at L005. L006 needed match reduction before
release rewriting, fixed at L007. L008/L009 rebuild after byte/key carriers
were made explicitly UInt8 lists. No timed-out or memory-killed shape retried.

The native queue K007–K029 encountered one missing closure parameter type in
metadata_control (m.wrapping_add(1)). It compiled the full crate before selecting
each harness, so 23 queued targets were rejected before verification. These
are NOT failing controls or native evidence. The queue incorrectly continued
on compile rejection; this consumed 23 attempt IDs. This is an owned runner
error. NLF_native now requires both 'Checking harness <exact target>' and a
final verification verdict, stopping on preflight/compile/no-verdict outcomes.
The type is now explicit u64. K030–K032 reached verification after the type correction was written; they are recorded by exact source hash, not retroactively counted as compile failures. Native allowance remains 28 attempts; the
remaining wrapper members will be grouped by real shared call dependency.

The native seed initially tried UTF-8 on a frozen binary source input. It
launched no scope. NLF_native_seed now transports every frozen file as base64,
validating the same pinned hashes before and after the copy.
