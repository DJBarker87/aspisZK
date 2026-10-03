# R427 raw MIR frame inventory plan

This is a read-only plan for the eventual `launch-gated-runner-attempt-b/saved-output/mir-frame.txt`. At preparation time, that file is absent. The attempt-B observer hook and saved-output auditor are the format authorities; this folder does not change either one.

The hook frames only the exact foreign item `core::iter::traits::iterator::Iterator::try_fold` with matching `ASPIS_R427_RAW_MIR_BEGIN` / `ASPIS_R427_RAW_MIR_END` markers and a DefId. It emits the complete pretty-debug body between them, then records statement source information, `Use` retags, terminator source information, and each Call argument with index, operand, and span. Keep the complete byte range from BEGIN through END; do not reduce it to selected lines.

When the capture arrives, the inventory should:

1. Verify there is exactly one begin and one end marker, with the target name and DefId equal, and preserve/hash the full framed bytes.
2. Parse the full body only enough to enumerate basic blocks and their terminators. For every Call terminator, record its complete original text, block label, function operand, ordered arguments, destination place, target, and unwind action. Do not identify a `next` call solely from a guessed method name; report the actual encoded function operand and match it to the `ASPIS_R427_CALL_ARG` markers by basic-block label and argument index.
3. Record the receiver operand's exact argument index and associated source span from the call-argument markers. Retain all other arguments and the complete terminator context alongside it.
4. Cross-reference every `ASPIS_R427_STATEMENT_SOURCE`, `ASPIS_R427_USE_RETAG`, and `ASPIS_R427_TERMINATOR_SOURCE` marker to its basic block and statement/terminator index. Preserve source-info and retag debug strings verbatim; do not infer provenance or source-level borrow semantics.
5. Store literal line numbers and byte offsets into the saved frame for every extracted context, and record the frame SHA-256. Any malformed or ambiguous association is a reported inventory failure, not a reason to normalize the frame.

No `mir-frame.txt` or attempt-B saved-output directory was present when this plan was written. Thus no Call operand, destination, target/unwind, or retag has yet been selected or interpreted.
