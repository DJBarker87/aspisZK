# Allocator/callback slice: checked boundaries

No endpoint or deployment row is removed. No T field is added or changed.
This is an incremental source/event-model bridge, not a complete native world,
not a successful actual-world witness, and not a privacy headline closure.

Before: seven constructor `map_err` sites demanded a polymorphic operator
computation and its whole source-result view. After: the six new caller bodies
install their typed error constructors, with argument destruction, capture
destruction, and unused-capture destruction modeled as Q computations. Source
transport derives the constructor result from the extracted body and the actual
operator selection. The source-result obligation for that polymorphic callback
is replaced locally by primitive drop views; native destruction/observation
association is not discharged. `PrivateSaltsNew` additionally installs the
success callback using typed new/move effects and destroys the unused function
operand on Err. Its physical move and Vec ownership remain unproved.

Before: CapacityWorld was separate from the callback installations. After:
PublishInstall and PublishWorld connect it to the first allocation in the
extracted publication body. `initial_denied` proves the full modeled body stops
before MAGIC/serialization, retaining the count prefix, post-allocator state,
errno and denial diagnostics. Overflow and the zero-sized layout branch remain
inherited CapacityWorld branches. Source projection remains PartialView;
termination/non-emptiness/native adequacy do not follow from it.

Before: V183 supplied a world-indexed source dictionary and pure continuation
lemma. After: ReserveWorld.reserve returns the same V183 post-world and exposes
its history/result in Q events; continuation propagates every Result/fault/
exhaustion outcome and prefix. SaltsReserve factors the original extracted
prover body and substitutes V183 at its first reserve. `initial_size` proves the
empty-buffer request capacity/bytes are public-count expressions;
`public_metadata` proves equality of allocation outcome and post-world under
same public header/length and same allocator world, independently of element
values. No equality of those premises across secret runs is inferred.

WorkerRequests proves the natural-arithmetic partition length and bound and
public byte-size formulas for explicit host_work Vec::with_capacity sites.
This is a source-indexed potential request list, not concurrent arrival order,
not std::thread/TLS/collect's full requests, and not the realized list on a
panicking/diverging callback. Target usize encoding and native binding remain
qualified by source/ABI validity; source-binding.json records the adopted bodies.

Still required, by exact class:

- HEAP-ENTRY / rdea-1: valid native Vec headers, capacity and layout/padding;
  Global/System answer validity and resource adequacy; same physical memory,
  ownership, errno, allocator private effects and event-encoding association.
- V400 / rdea-1: initial allocator world and stateful answers independent of
  witness; later push/extend/append request shape/count and failure timing.
- V400 / rdea-2: advancing OS world for op257/host_work.map, thread creation,
  TLS initialization/access, joins, exhaustion, worker panic and scheduling;
  occurrence/timing witness-independence. Public partition sizes alone do not
  prove these facts. Panic=abort source branches must remain observer-visible.
- V370 and L3: source-to-machine/drop/move/capture/register/spill association;
  physical zeroization, including PrivateSalts destructor, not established here.
- Full advancing actual-family entry and trace projections/non-emptiness.
  ReserveWorld returns an extra world to its continuation; do not discard it to
  fit an older Q leaf that returns only a Vec. Thread it through the salt loop
  and new/move continuation, then through the original prover entry.

V183 Kani source credit is still SUSPENDED(K-3) per runjoin73 D564 handoff.
The three reused V183 modules are the same runjoin32 build instance, with source,
object, dependency and external-object pins in allocator-extension.json. This
is reuse, not re-extraction or reinstatement of the suspended credit. No raw
NEP full-data walk/cohort-coherence claim is made. All #print axioms are
SUMMARY-BASED (ax1-prime), and only accepted attempts earn credit.
