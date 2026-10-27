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

## Isolated default method and final pinned-translator failure

Read-only inspection of trait impl68 identifies Iterator::copied as the default
method with an item-type equality incompatible with IterMut and Enumerate.
XRe_003 changes only selectors: remove broad includes, exclude that one standard
library default method. Charon now succeeds, wrapper exit0, has_errors=false:
8b049f3188cb83227ab485562c755811d33e643fef44a30de5748a3349cae659,
16981964 bytes. This remains a selector-derived artifact, not a byte-identical
reproduction of 80465ea3. The original artifact is retained unchanged.
XRe_llbc_inventory.json records all459 non-null function entries (685 slots),
with expanded-body and full-name hashes. EXACTLY SIX release-namespace
functions are opaque, precisely the six approved leaves; no extra release
leaf is hidden. Foreign library opacity is separately visible in the inventory.

XRe_004 is the fourth/final combined invocation. Pinned Aeneas exit2, before
emitting any files, at FunsAnalysis.ml:134: function called here missing from
crate, r1_semantic.rs:83:23–83:49, polynomial.iter().copied().fold(...).
Thus the selector exclusion fixes Charon's invalid trait references but removes
a library declaration actually called by the newly exposed semantic boundary.
A valid has_errors=false flag does not establish complete call closure.
This is NOT a seventh untranslatable release function; no extra leaf is added.
No Types/Funs, generated model, or declaration association is claimed.
No translator/library patch or shipped-source edit is made.
Extraction budget used4/4 (3 Charon,1 Aeneas); no further invocation permitted.
