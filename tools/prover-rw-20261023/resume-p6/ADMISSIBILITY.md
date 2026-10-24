# Scope of the proposed instrumentation relation

These are inspected source arguments and explicit proof obligations, not an
accepted native semantics theorem. No previous theorem premise is changed.

The instrumented `Zeroizing<Z>` representation and all selected caller carriers
are unchanged. Hooks add no struct field, pointer, reference or phantom owner.
Array snapshots visit the typed elements under a shared reference created from
the currently active destructor borrow. The scalar u8 observer copies `*self`;
it never casts raw storage, reads padding or keeps a child pointer. Pre/post
copies are ghost secret material and must be erased from the observation model;
this packet makes no hardware/cache/register/stale-copy claim about them.
An ordinal denotes one hook invocation, not persistent logical owner identity.

The original scalar zeroize volatile-write/fence, array iterator zeroize and
Drop call remain. The explicit u8 DefaultIsZeroes impl has the same production
empty marker impl as the original macro expansion; the cfg(kani) byte observer
adds only a safe read. The original Drop tail call is made a unit statement so
the posthook can run. Reverse-patch identity certifies exact original tokens,
not semantic erasure. These source changes and package identities are pinned
separately from the unchanged production/registry source.

In sequential source reasoning the ghost store is disjoint static storage:
no source byte-array value contains a reference to it, observers receive only
shared typed borrows, and neither `record` nor its Copy snapshots has a user
Drop. Ghost writes cannot directly write the source payload or request. The
metadata has assertions/Option expectations and a three-event bound, however;
noninterference therefore also requires these checks to be unreachable on
all valid normal paths. The intended058 assertions check that obligation in
Kani's memory model alongside actual events; a timeout is no proof of it.
The native original library is no_std and Kani models fences sequentially.
No concurrent, unwind, abort, capture, loan or general provenance theorem follows.

Even a successful paired source execution only establishes projected normal
control/result/error and byte observations for the same supplied primitive
outcome. It cannot prove the OS supplies those transitions, contextual E1,
world advancement, the error experiment, whole-driver reachability or finite16.
The actual driver invariant has no producer in this packet. Equal32 payloads
also cannot distinguish field/leaf identity from event bytes: source/MIR role
association still needs an accepted lifetime/move relation. The older D204
moved-owner/fresh-root limits remain, and no retained-child-pointer result is
revived. No whole helper equivalence is hidden inside a contract structure.
