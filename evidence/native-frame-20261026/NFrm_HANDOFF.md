# Native frame investigation

S2 OPEN; target not yet established.

## Before and after

Before: `T2Nat_NativePair.accepted_pair_unified` retains the actual native
constructor, Claims std, and library frame obligations L174/L177/L179.
After: pending focused trust-scope check. No closure is claimed.

## Ledger delta

Removed: none. Added trust items: none. L174/L177/L179 remain open.

## Scope and validation

Only NFrm_ modules and this receipt directory may change. No shipped file,
other worker prefix, key, or live Session A worktree is changed.
Budget is 100 Lean attempts including dependencies and 30 Kani runs.
All compiler calls use the retained S2W launchers in the coherent SInt2 host
workspace, -M7000 and separate 6G/8G/swap0/64 scopes. No full replay.

## Working obstruction

The exact top's S2W_TrustedStd record constrains only copy_from_slice.
Allocator is two private-state operations without a relation to Claims
reserve/intoBox; entry admission constrains initial account/borrow geometry;
RuntimeSyscall constrains successful hash return values. The separate
Port1_Library.TrustedStd constrains only Option::ok_or and Result::unwrap32.
No field of these interfaces mentions native Claims allocation carriers.
A checked scope test must distinguish this omission from a shipped bug.
