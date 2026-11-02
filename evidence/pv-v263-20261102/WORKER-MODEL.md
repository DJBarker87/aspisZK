# Resumed D567 model status — not an installed V263 link

New modules are all R1Z.PV_V263_*. No accepted pre-existing Lean module was
edited. The original `NativeBoundary.retained` theorem still describes the
actual opsNative dictionary: op257 remains the residual operation.

## Accepted components

- PublicRequests: source-capacity shape and thread-list functions depend only
  on Shape; nonnested thread-list length15, nested list empty. The equality of
  actual paired Shapes is NOT proved. V400Obligation names requests, answers
  and failure timing separately, with no endpoint assumption or new T field.
- WorkerRequests: typed TLS read/replace/restore, allocation-site, release,
  spawn, join and cleanup answers. Grants advances TLS/handle state; Denies
  answers spawn denial. The codec is supplied, not certified. `aborting` only
  classifies panic/denial as abort: its empty denial message is NOT a native
  diagnostic payload. Actual hooks/stderr/formatting remain obligations.
- WorkerControl: full Result/fault/exhaustion sequencing; catch distinguishes
  unwind from abort; finalize retains post-state/events and handles double
  panic. Stateful callback traversal, not a fixed pure callback. Merge chooses
  the first source-order caught panic. Destructor/native correspondence is
  not established merely by defining these combinators.
- Team: thread-request projection of source `for k in 1..16`. Grants derives
  exact consecutive handles and +15 counter; first denial keeps its event and
  has no source Result. No callback-success hypothesis is used for this result.
- Family/FamilyWorld: symbolic callback bounds; explicit inner capacity site;
  conditional stateful callback traversal and TLS-restored successful family.
  The callback-success law is NOT proved for actual captured callbacks and is
  NOT installed as a premise of P or privacy. These theorems are components.
- DeferredJoin: one allowed candidate schedule defers workers until their
  joins. Actual task actions execute on exact successive post-worlds. Join
  errors become caught panic values. The two-panic check runs both actions
  before source-order merge. This is not general scheduler/source adequacy.
- MapSpine: candidate list-data source spine for that schedule and panic=abort.
  ACTIVE/nested branch, both range layers, fifteen forks, caller worker,
  all-handle joins, merge, and vector-method effect sites are explicit. Stage
  is unused with public-work-trace off. It returns List, not the source Vec.
  VecCall describes SOURCE METHODS, not raw allocation syscalls.

## Still required before any V263 closure or native installation claim

1. Prove/source-bind VecCall's lowering and heap stores, including item pushes,
   exact collect specialisation, capacity metadata, handles growth, all implicit
   Vec/iterator drops, scope state/packet and TLS lifetime effects. Source-level
   lists alone are not a model of the EVH heap. Native callbacks may contain
   further effects. Full scope cleanup on unwind is not supplied by this
   panic=abort schedule candidate. Keep the deployment profile explicit.
2. Prove that the proposed join-late schedule is realised by an adequate native
   world and bind the event codec to EVH's actual NativeEvent observations.
   Keep the general failure branches; the candidate schedule does not certify
   every scheduler trace. No EVH compiled cohort was mixed or copied here.
3. Prove complete output length/bound and convert List to the exact source
   alloc.vec.Vec carrier. OutputShape is the focused invariant work, not a
   termination proof. Its Post only constrains results WHEN they return ok.
4. Reify the actual commitment and sumcheck closures with their captured
   arguments/instantiations, including exact op227 bridge use; prove their
   successful execution at all reached indices. Do not supply a successful
   vector or a generic callback-totality hypothesis to the endpoint.
5. Install that implementation as the actual native op257 at opsNative with
   partial source projection on returned runs. Thread its post-world through
   the actual NativeControl capture (old Sequential64.worker still resets w).
   Native fault/exhaustion must NEVER be projected to a fabricated source div.
6. Construct the actual captured success witness and conclude Nonempty P.
   A grant-only thread prefix/family component is not such a witness.

V400-257-* resource/request/failure-timing obligations are specified precisely
in V400-WORKER-RESOURCES.md. They stay P obligations, not trust fields. V370 and
D381/D386 compiler preservation remain. No V183 credit is restored (K-3).

OutputShape (focused continuation): `Post` constrains only actual returned-ok
outcomes; `bind_success` extracts both computations at the exact intermediate
world. `traversal_length` and `items_length` prove exact element counts for
arbitrary stateful callbacks, and `family_shape` proves the one-family tuple
shape. These are the starting lemmas for a total output-length proof and the
source Vec carrier conversion. They do not assert an actual successful run.

## D571 continuation

SourceItems and the separate SourceSpine candidate add explicit item-push
method effects after each callback. GrantControl/GrantItems/GrantTeam/GrantRun
prove COMPLETE revised candidate success in a constructed granting world,
conditional only on its still-undischarged bounded CallbackLaw. Both TLS
branches are covered; no successful vector or worker-output oracle is supplied.
This is not successful execution of the deployed captured callbacks.

VectorLoop supplies an actual alloc.vec.Vec INNER loop with explicit push
results and completed counter. Its successful output length/counter bounds
are constructive and symbolic. The outer SourceSpine is still List; physical
heap stores/capacity and native Vec lowering remain unbound. Source/Result
reification is not full native adequacy. SOURCE-BINDING-D571.md and the 29-row
source-binding-audit.json record the exact remaining source frontier. Actual
opsNative op257 is still residual. No new endpoint success premise was added.
