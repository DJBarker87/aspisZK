# D579 continuation: constructed adapter, native binding still unproved

Entry 72737dd94f9c3f864670dcd5c9ffd66d053a5db1, branch
codex/pv-runjoin-20261026, same sparse worktree. The requested D579 theorem
has NOT been proved. No reached native counterexample has been established.
This note does not replace or weaken BLOCKER-D579.md.

## Step 1 helper actually constructed

PV_V263_HandleAdapter constructs a RetainedMethods.Runtime and RawGrowth.Runtime
from one resize action, one stopped Empty-valued computation and one world-indexed
allocation descriptor view. The handle vector hook reads its descriptor at the
invocation world; it does not close over one particular handle owner. It issues
no request when reserved, and delegates to RawGrowth.grow when full. Other vector
sites, OS operations and lifecycle methods retain the supplied base runtime.
Overflow uses Empty elimination, so no successful ownership value can be
manufactured. All stopped outcomes, post-worlds and event prefixes are retained.

push_erasure proves the displayed D579 World.Run equation with these constructed
runtime/growth substitutions, conditional on descriptor w = handles.allocation
and a length bound. It erases only the successful ownership metadata. It never
identifies the buffer's reservation lower bound with physical capacity.

PV_V263_HandleAdapterTotal removes that length-bound hypothesis by deriving it
from physical ownership in the reserved branch, and from requestedCap/enough in
the successful growing branch. It retains every overflow/failure branch. Its
only representation hypothesis is the descriptor view equation. Neither module
is a native-source association or a proof of that representation hypothesis.
They are direct step-1 helpers, not replacements for the requested theorem.

## Exact remaining source obligation

Construct ONE deployed-source-bound native runtime/growth pair and its native
allocation interpretation. For every handle owner, task and world reached at
handles.push(scope.spawn(...)) in the frozen spawn loop, establish the descriptor
view equation from that interpretation, layout = layouts.handle, native
allocation validity, and preservation of that interpretation across spawn,
resize, descriptor assignment, typed store and length assignment. The runtime
resize and stopped computations must be the native Global allocator/overflow
paths with the identical world/events, including their failure prefixes.

Then prove EXACTLY the equation and binders in BLOCKER-D579.md on its unchanged
reached domain. The newly proved adapter equation is not that theorem: resize,
stop and descriptor are still parameters without deployed native association.
Assuming their association as an endpoint premise would leave the task undone.

The same view must be maintained through the entire RetainedSpine.forks loop,
not reselected independently per push. RetainedSpine's native interpretation,
whole-spine stores/drop/TLS/scope/packet lifetimes and allowed scheduling remain
unbound. No replacement spine was installed. Steps 2 and 3 remain blocked by
step 1; actual opsNative/op257 and capture/Nonempty P remain unchanged.

## Evidence discipline

Frozen committed evidence copies of all eight deployed-source inputs match
checkpoint 9c131667ca00f4daae78da6299b09a9fe0d00da9 and the D579 pins. Five
corresponding current worktree files differ from that checkpoint; the binding
target is the pinned evidence copies, not these newer worktree variants.
See source-check-D579-resume.json for both comparisons. No Rust source was edited.

79975 was rejected for unsolved proof goals: the descriptor view was rewritten
before the invocation-world bind was exposed. Its original output and source
revision are retained; it earns no proof credit. 79976 accepted the changed
source. The accepted source is retained byte-identically thereafter. An attempt
to stage a strengthening in the same accepted module was rejected before any
scope/ID submission by the accepted-object guard. The original accepted source
was restored and the strengthening put in the new Total module. No accepted
object was overwritten; this was an own-input staging correction, not a host
infrastructure fault. 79977 was then refused before compilation for aggregate
reservation (projected 59,995,324,416 > safe 59,055,800,320 bytes). The local
focused.py retry loop was stopped while sleeping, since it would reuse that ID;
next admission must use 79978 after the complete 180-second cooldown. The wrapper
was not changed. Native budget and audit IDs remain untouched.

No row or endpoint premise removed, added or changed. Three TrustItems, seven
links, observer, simulator, release pins, V370/D381/D386, V400-257 and suspended
V183(K-3) unchanged. Skeleton consistency remains reduced to non-emptiness.
No key/fund, Kani, SBF, ELF or full-manifest operation. No release/coherence or
raw axiom audit claimed; accepted #print axioms evidence is summary-based.

## Final focused validation

79978 accepted PV_V263_HandleAdapterTotal after the cooldown and a fresh
allowed:true/exit0 reservation in the same shell. Its theorem removes the
helper's length-bound premise; it does not remove the native descriptor-view
obligation or establish source binding. Complete outcomes were split
symbolically; no recurrence/numeral normalization or full replay was run.

Per-module results: 79975 exit1, wall12.47s, peak4,512,612,352bytes, swap0,
revision4f0bb44875; 79976 exit0, wall5.21s, peak4,571,205,632bytes, swap0,
revisiond69ab428d5; 79978 exit0, wall3.72s, peak4,587,626,496bytes, swap0,
revisiona5b8b16cf1. Scope totals are separately in receipt-*.json (12.53s,
5.26s,3.77s). Exact targets, dependencies, commands, source and object hashes,
and original summary-based #print axioms output are in modules-/receipt- files.
Both accepted theorems depend only on propext and Quot.sound. The rejected
attempt's sorryAx summary is an elaborator error artifact and earns no credit.
All scopes use MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000.

Three normal Lean attempts charged, two accepted and one rejected. 79977 is
skipped/refused/uncharged. 116 normal Lean and14 native remain; next79979,
then91300–91396. Both sets of audit IDs remain unused. No wrapper changes;
the authorized913xx ID/budget-only extension is still needed before913xx.

Final read-only checks pass:4309 project objects,9662 direct dependency
fingerprints,5673 external objects,5438 IR companions;9980 namespace resolutions;
accepted-source/object/no-live-own-scope reconciliation; forbidden-proof-token
scan of both new modules. These are focused cache/source checks, not a coherent
release replay or raw axiom walk. No evidence input exceeds20MiB. The refused
ID leaves115 usable normal numeric IDs despite116 unspent charged attempts;
audit IDs cannot be repurposed. Next normal ID79979.
