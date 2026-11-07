# PLIB specification semantics, revision 1

These are normative specifications, not row proofs. Privacy target not yet
established. The files PSPEC_*.md and this file form one specification. The
source and provider revisions in INPUT_MANIFEST.json are part of the freeze.

## Machine and environment

For row r, `MachineSpec_r(m, env)` fixes the source carrier (including tagged
aggregates, moves, typed pointers and discriminants), control/configuration
facts, and the emitted program of r and its reached callees to the frozen
syntax identified in its file. Its leaf equations are the providers' NAMED
documented semantics, not a dictionary of desired conclusions. Resolution
agrees on the actual issued function, including callback specialization.
The machine is universally quantified; the specification does not install
a handler or change a resolver inside an existing run. Existing specialized
CLOSED providers need `PV_THR2_RunAgreement.prefix_identity`, with program
and handler agreement proved at the actual reached sites.

On the thread path, `step` is literally
`PV_THR2_SourceStoreInterpreter.step`, from W4 at the input pin, with its
`PV_THR2_SourceStoreLibrary.interpret`. Its `Values` is bound to the named
runtime value interpretations, not an arbitrary choice satisfying a desired
write. No Store-transformer or successful write premise occurs in MachineSpec.
The five source-store meanings are CellReplace289, RangeNext93,
IntoIterNext9, VecPush167 and VecAppend10. Invalid decoding is an explicit
model/source adequacy failure, not an identity write. The slice call closure
contains none of these sites (D965); its existing OWNER/copy/set_len machine
is retained, with the symbolic neutral-step agreement required if using the
common enlarged interpreter. The intrinsic catch callback is executed;
an arbitrary native return cannot stand in for running that callback.

`Env` has an explicit resource channel: for each actual allocation or
reservation request, indexed by source site, occurrence and actual request
arguments, it supplies the FULL resource answer, post backend world and event
suffix. Thus fallible reservation Err is distinct from infallible-allocation
abort, and two runs with the same env cannot choose different returned values.
There is no blanket may-abort arm. An abort is admitted only at a reached
source allocation/panic/abort or inside an identified child's own model.
The environment also supplies the full OS/TLS/leaf reply channels permitted
by the named documented facts. Its dependence on secrets is not assumed away:
witness independence remains the existing rdea/V400 obligation.

OWNER places/next are ghost state: the framed native lift preserves them on
EVERY answer, including pending, except for named allocation/OWNER actions.
Heap bytes and backend state may change only according to the actual child
model's footprint. A native reply is not an arbitrary OWNER registry.

## Entry and frame

Entry arguments include their source representations, explicit entry store,
OWNER/backend world, lower caller stack, suspended stack and prior events.
All are universally quantified. `Pre_r` conjoins the row's input clauses with:

1. Valid initialized typed references (non-null and aligned even if empty),
   address-space bounds, readable extent, and writable/disjoint extent for
   mutable references. These are Rust reference validity, not arbitrary
   alias or success assumptions. Ownership is registered at the entry-selected
   place with initialized bytes and valid descriptors; no later receiver is
   supplied to fit the run.
2. OWNER well-formedness: registered ids below OWNER.next; registered source
   activations below the activation counter; registered allocation bases
   non-null and aligned to their layouts. Allocation actions establish this
   from named allocator facts; natives preserve the ghost fields.
3. Thread-25 numbering: current, saved and suspended live activations below
   nextActivation, saved callers strictly decreasing. A new caller discharges
   the callee clause by `PV_STX2_LiveNumbering` push/preservation lemmas.
4. Actual argument cells, saved return destination and waiting action agree
   with the call-entry configuration. No lower-stack source code or successful
   reply is prescribed. No conclusion, future read or future decoder success
   is an entry clause.

`Frame_r` at a non-abort boundary preserves all pre-existing source cells
outside the source-defined mutable argument footprint and return destination;
fresh/dead own-frame cells are tracked separately. Heap frames use the named
provider byte/header/ownership clauses. Shared references do not authorize
overwriting their value or data; Arc clone can change only the documented
strong-count field. Lower and suspended continuations are preserved up to
the row's return administration. Events have exactly prior ++ emitted suffix.
There is no universal unchanged-world assertion for effectful OS children.

Across a callee boundary compare only required source cells, representations,
ownership, world and events; NEVER nextActivation or the whole Store including
it. Both sides carry numbering. Existing provider internal equalities are
retained but are not exported as cross-boundary equalities.

## Reference evaluation and Post

`Ref_r(args, entry, env)` means the source-order computation specified by the
row's value clause and its pinned emitted syntax, interpreting each CHILD
call at SAME operands and its actual call-entry state by that child's
deterministic model. It is an independent reference for a candidate
implementation `impl`, not the proposition that impl equals itself. A pending
child has not returned a value; no later source instruction is evaluated.
OPEN children are named specification slots, never falsely labelled CLOSED.
The dependency graph is acyclic (DEPENDENCIES.json).

`Post_r` requires `observe(impl args entry env) = Ref_r(args, entry, env)`:

* On every returned `Ok v`, exact source-encoded v, explicit boundary state,
  ownership/value clause, frame and ordered events.
* On every returned `Err e` (including all payloads and nested Result arms),
  exact source error, explicit boundary state and effects UP TO that error.
  Allocations before the error are retained. No success-only domain.
* On failure/fault not terminating the process, exact status and current
  source-store/world/event prefix; source cleanup only when the recorded
  panic configuration actually executes it. Undefined machine representations
  remain a named adequacy gap and cannot count as a successful source result.
* On process abort, only `Abort(events_so_far)`; NO post-abort store, ownership,
  backend or frame obligation. The internal machine can retain a store, but
  that is erased by observe. Formatting allocation before a log therefore
  can abort with the prefix excluding that log.
* On pending, exact running configuration after the ACTUAL consumed pending
  reply, with unchanged pending control and actual world/events. The active
  frame is not completed and its child resolver must be `none`. A BODY push
  never consumes the fallback handler's answer. A pending reply ends this
  invocation; it is not repeatedly polled until a preferred answer appears.
* On divergence, exact observable finite prefixes and no finite return.

The chosen finite boundary is the FIRST own completion, delivery of a
nonreturn outcome, or actual pending answer, whichever source execution
produces. It never passes delivery into lower caller code. Own completion
before return administration is permitted (thread-23'). An infinite trace
has its divergence case rather than an invented finite witness.

Library slot law is `o = model args entry env`, a GRAPH of a function; it
is never the native provider's relational Post. A separate adapter theorem
connects the CLOSED theorem to that graph, retains every Result arm, and
establishes caller-domain discharge. A graph declaration alone does not
prove the adapter. The map explicitly distinguishes these obligations.

## Allocation audit policy

Audit transitive bodies, not just returned-success branches. Keep to_vec and
Vec/Box allocations, CString/name conversion/reservation, clone allocation,
Vec growth, and allocation preceding a later Err. String-carrying errors
require an allocation arm if cloned; moving a Result through `?` does not
clone it. `format!` allocates before its log, never afterwards. The RSL
ProgramError clone and decoder examples are TEMPLATE lessons, not extra
calls inserted in these privacy functions. Leaf internals with no sufficiently
strong CLOSED model remain MISSING-CHILD-LEMMA in the map; an arbitrary full
reply closure is not evidence of an exact allocation schedule.

## Freeze

FREEZE.json pins revision-1 specifications by SHA256. Future changes require
a demonstrated error against these frozen source inputs and an entry in
SPEC_CORRECTIONS.md containing the exact old text, new text, source witness
and affected consumers. Missing proofs do not justify weakening a spec.
