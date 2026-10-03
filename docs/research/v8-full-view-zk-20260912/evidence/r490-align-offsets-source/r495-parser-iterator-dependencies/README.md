# R495 parser iterator dependency capture

This is a diagnostic LLBC capture only, not a Lean proof or a source
correspondence result. It preserves the R495 runner, command and source/tool
pins, complete standard-output/error logs, summary, result, and LLBC unchanged
from `.r21-scratch/r495-parser-iterator-dependencies/`.

`capture-summary.json` records the successful scoped run: exit 0, wall 0:13.39,
peak RSS 625,300 KiB, zero swaps, and LLBC SHA-256
`28ae0b878a54842a705ed71f4ab4fe374edc8b6530170d729bbce79945e1e24b`.
The capture added only the selected `split_at_unchecked` and
`unchecked_sub::precondition_check` include patterns to the R494 set.
