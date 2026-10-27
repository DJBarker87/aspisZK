# Six-leaf release extraction finding

Target not yet established. Two selector-only lowerings of the same 7978-file
pinned release snapshot expose a predecessor obstruction in pinned Charon.
No Aeneas invocation is launched on an LLBC with has_errors=true.

XRe_001: exactly six explicit release leaves; inherited broad selectors removed.
Charon exit0 is insufficient: artifact a2650ac0… (17002597 bytes) has_errors=true.
The validation wrapper exits1. Two mismatched iterator trait clauses:
IterMut expected Iterator<&T>, actual Iterator<&mut T>, core/slice/iter/macros.rs:153;
Enumerate expected Iterator<&T>, actual Iterator<(usize,Item)>, enumerate.rs:62.
Full diagnostics: XRe_001/stdout.log, lines1332–1359.

XRe_002 changes inputs by including core::iter and core::slice::iter explicitly.
The same pinned tools/source/MIR/features remain. Artifact ebcac9ea… (26043062
bytes) also has_errors=true; wrapper exit1. Additional variants include
Iter expected Iterator<&mut T> or Iterator<(A,B)> and ChunksExact expected
Iterator<&mut T>; full errors are retained in XRe_002/stdout.log.
This is a failed selector experiment, not a seventh Aeneas-failing release
function. It does not authorize adding an arbitrary extra release leaf.
The six original functions remain the approved P6 targets.

Both artifacts remain host-only. The original 80465ea3 LLBC is unmodified.
No source/translator/library patch, new trust item, or alternate-file
substitution. Resource receipts include all required AGENTS fields; swaps0.
Complete release Types/Funs and association are not delivered by these runs.
