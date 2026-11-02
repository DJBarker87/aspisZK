# D550 runtime and heap extension (registered before implementation)

The old World lacks heap/handle/errno state and the old FinishedView excludes
allocator aborts for pure source values. Add a NEW runtime state embedding
World and explicit heap blocks (identity, address, layout, bytes, ownership),
handle identities and errno. Do not edit accepted modules or the extraction.

The finite outcome separates returned source Result, runtime fault and fuel
exhaustion. A runtime fault retains its exact final state and event prefix;
it is never represented as source divergence or exhaustion. Source projection
is partial: only returned source Results project. Every runtime fault projects
to none, including allocation failure. Prove bind-prefix preservation and
partial-view composition before any allocation implementation.

Allocator answers take the complete runtime WORLD and a layout, and return
updated allocator state, errno and either an address/block identity or failure.
This is an allocator boundary, not a pure-value source answer. No allocation
success hypothesis is asserted globally. Heap ownership, identity, capacity,
zero-size layout, checked layout overflow and address disjointness are explicit
obligations for later source binding, with success and abort branches retained.
NativeEvent remains unchanged; heap/runtime events are encoded using its side
constructor with an explicit encoding/adequacy obligation. That encoding must
retain reached metadata; no empty payload earns observer adequacy.

This extension and its algebra alone are NOT native heap fidelity. Credit needs
a statement-by-statement binding of the deployed Rust 1.94.1 allocator/vector/
drop paths (own-1), preserving mutation restoration, partial failure cleanup,
formatting (fmt-1), and compiler boundary V370. Actual runjoin opsNative and its
allocator world remain the target. Existing T is unchanged; all native
association, encoding and state-abstraction obligations remain P obligations.
The old event interpreter can be embedded preserving runtime state, but this
must never be credited as proof that its native leaves do not touch the heap.

Next consumers: runtime operator frames and the reified six operator spines;
then allocation/drop source binding and only afterward the full entry, trace
links and actual-family (v') nonemptiness reduction. Rows removed NONE.
