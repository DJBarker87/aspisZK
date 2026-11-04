# Attempt notes

L001 was a prelaunch wrong-module-path error; conservatively charged to Lean/support. L002 confirmed missing slot_offset in the compact-only module. L005-L010 and L012 were local elaboration failures while resolving irreducible constants, array projection and UScalar wrappers; their auto-recovery sorryAx output is rejected, never a theorem audit. L013 is the successful replacement, using named generic wrapping laws L011 and six named symbolic step lemmas.

K005 compiled no harness: including the exact KMX stubs requires cfg(kani) feature(allocator_api) at the library root. The scratch-only cfg attribute was added; frozen shipped files remain unchanged. No timeout or memory failure has occurred.
