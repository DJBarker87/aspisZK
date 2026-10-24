# Native entropy continuation: design and admission boundary

Unadopted candidate after 57e7c88e14, reviewed local proof bb9ec678e2.
D187 and D191 authorize owned host control/provider work after this design.
No installed extractor, shipped source, verifier, protocol, metric, key or trust
change is made by this design. Both deployed targets remain not yet established.

## Evidence and prerequisite

The new full-hierarchy resource scanner is job-owned in
`tools/prover-rw-20261023/native-entropy/reservation.py`. It visits every cgroup
under the unified root, using hierarchical `cgroup.events: populated`, not
only direct processes. A finite populated ancestor covers its descendants
once; uncapped background current usage stays visible. Missing required
controller data, unreadable directories, and inconsistent population fail
closed. Controller-disabled descendants inherit their ancestor's coverage;
threaded groups need no direct process enumeration. Admission requires
finite reservations plus the requested cap strictly below 55 GiB. Every
scope rechecks after cap verification, before work. Docker stays behind its
own verified 6G/8G/noSwap/Tasks64 go barrier and a second admission snapshot.
This snapshot is not a global scheduler lock against unrelated launchers.

The prior app.slice-only aggregate claims are unverified historically.
Live admission-004 records 24.375 GiB reserved and 32.375 GiB including a new
8 GiB job. It cannot repair earlier missing evidence. Failed scans 001–003
are retained; no build or extraction ran during them. Fixtures cover nested,
empty, direct-zero/child-live, all slices, strict ceiling, unavailable data,
and disabled-controller inheritance. Existing 5G/7G Lean limits stay stricter;
outside 22:30–14:00 London use the existing shared global lock.

## Actual source and Drop inventory

The exact selected64 LLBC and its original source/dependency association are
reused, not re-extracted or new identity evidence. `selected-drop-inventory.json`
retains every Drop site, expanded type, complete fn_ptr, kind, unwind subtree,
place and JSON path. Its 69 statements comprise:

| Type/glue | Sites | Effects and treatment required |
|---|---:|---|
| Zeroizing<[u8;64]> | 25 | 64 physical volatile writes and compiler fence through zeroize; retry, error, success and unwind cleanup |
| Zeroizing<[u8;32]> | 31 | 32 physical writes/fence; moved live success seeds must remain live; discarded seeds wiped |
| Result<StateOnlyAttemptSecrets, StateOnlyAttemptEntropyError> | 1 | Discriminate variant; Ok recursively destroys both private Zeroizing fields; Err retains actual OS error until intentional mapping |
| Generic T0 callback/state | 9 | Arbitrary destructor cannot be erased or assumed trivial; actual instantiation and capture tree required |
| Capturing proof-account closure<T0> | 2 | Captured mutable policy ownership/drop order and loans must be retained |
| Generic T3 in map_err | 1 | Actual monomorphized FnOnce capture effects required; generic destructor cannot be declared no-op |

There are 56 statements in generate_for_mask_nonce, ten in client/closure/
retry entry, one in map_err and two in Zeroizing drop_glue. Multiple unwind
paths are distinct sites, not 69 distinct destructor types. Selected Drop
glue is mostly BuiltinOrAuto UntrackedDestruct through trait function pointers;
that identity does not prove its implementation effect-free. The inventory
is not a transitive whole-owner closure: retry_attempt/attempt construction,
Vec proof/material allocation and borrowed durable-store filesystem effects
cross opaque leaves. DurableStateOnlyMaskNonceStore contains PathBuf/error
state and retains reservations after failure; SensitiveQm31Vec has its own
volatile field cleanup then Vec allocation cleanup. Those operations require
an expanded inventory before whole-owner acceptance. Ending a reference
loan does not destroy its durable referent. Copy byte/public nonce/error
scalars have no user destructor, but StorageDead/Bottom/dummy bindings and
loan bookkeeping still must be preserved. No erasure follows just from Copy.
The separate 96-byte generate method is outside this target.

## Compared implementation routes

(a) Sound selected Drop and loan translation: execute actual drop_glue under
the existing interpreter, including conditional initialized/moved places,
variant dispatch, recursive field drop order, loan writeback and unwind.
First support a minimal Guard counter (0 becomes 1), preserving raw diagnostics
and requiring entire translation success; reject unsupported borrow/escape
before any accepted artifact. Then handle Zeroizing's concrete array effects
and prove a source-to-emission relation with physical zeroization observation,
not merely equal returned values. Finally repair borrowed FnOnce/FnMut return
and back-function signatures plus impl_def binding, and compile whole selected
output. This reaches deeper interpreter paths and volatile operations. It is
not a narrow refined-error patch and must not expand extraction trust.

(b) D187 owned native provider/control: replace internal borrowed callback
composition with explicit owned transitions. Retain arbitrary mutable public
proof-account policy once per entered attempt and return its advanced state.
A fill64 transition receives a newly zeroed physical secret buffer and owned
provider; returns advanced provider, post-fill buffer and ordered draw/error
event OUTSIDE Result, on success and partial-write Err. Preserve the actual
getrandom Error before StateOnlyAttemptEntropyError::Os and Error::Entropy.
OS fill remains the existing entropy primitive; no stateless replay dictionary.
Do not clone/reset state. Inner zero-block retry limit is 16; public zero nonce
fails before any draw; outer limit is 8; only Rejected retries. Duplicate or
durable failure aborts with advanced store retained. Every discarded secret
must physically wipe, including early errors. Returning buffers as a model
state is not a license to leave native secrets live or leak them.

Route (b) avoids the borrowed Fn* signature obstruction but does not itself
solve Drop extraction: actual wrappers still have Zeroizing and arbitrary
policy destructor effects. A sufficient source transformation must prove the
exact cleanup schedule, moves and event relation for these concrete types;
explicit clear followed by physical Drop is permissible only with both effects
accounted for. No forget/leak, drop_as_no_op, cleanup premise or whole-owner
output-equivalence assumption is allowed. Therefore start depth-first on the
minimal baseline Drop probe, then narrow real Drop semantics. Do not build a
new success-only provider wrapper over the unresolved shared Drop boundary.

## Required source/event relations and validation order

For every entered source operation relate provider/policy/store identity,
initialized/moved buffers, loans, ordered native draw/error/cleanup/store events,
result/error and advanced state to emitted control. Rejected and partial-write
suffixes are included. Bottom/dummy bindings and outstanding loans cannot be
filtered out by selecting only successful emitted functions. Validate minimal
synthetic semantics, actual selected output, smallest Lean theorem, dependent
bridge and focused full-statement/import/axiom audit, in that order. Preserve
all failed/partial outputs as rejected. Existing candidate005 local proofs and
candidate007 rejection remain exactly at their documented scope.

Associate literal ProverCommitPublicNonce40.E1's conditional 64-byte law only
after exact source/event transport. No added freshness, independence, retry
uniformity or hidden output equality. No premise changes occur in this stage;
before and after, existing native statements are unchanged. Standard axioms
only. Source-to-binary adoption additionally needs all three current ELF
identities, fixed-coin >=1000 differential runs, native event/status/refinement,
H5 interleaved <=10% slowdown and quiet-host <15s. Contended-host timings are
not performance gates. Current pins are retained, not rebuilt identities.

## Budgets and next producer

Start at Lean219/260, Kani44/60, extraction12/24, backend7/12; every failure
counts. Resource fixtures/read-only inventories consume none of those slots.
No full frozen manifest is authorized. Next producer: minimal no-refined-error
Guard source on pinned accepted baseline, complete status and diagnostics;
then decide whether narrow real destructor semantics are feasible within the
five remaining backend builds. A matching omission requires a precise affected
source/trust inventory and explicit correction of closure claims; it does not
prove unrelated installed-backend unsoundness by itself.
