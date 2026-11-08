# Session8: typed destruction and preserved cleanup; PARTIAL

Base1451aa2e0c9dfb974b4d846aed22c8407d5490ca. No frozen spec, package,
ledger, checker, row consumer, implementation or Lane B change. No endpoint
premise or trust field added/removed. All170 slot records/statuses stay as at base.

## What now has a checked local binding

DropMetadata retains127 exact hash-cons entries from the existing LLBC, with
explicit failure for unknown keys. TypedDestruct normalizes metadata and
substitutes Free type variables; bound dyn variables are preserved. The generators
check type-variable arity before emitting a template. Actual method metadata is
from the retained Destruct::drop_glue method0 table, not numeric-function-id
inference. ExactDestructMethods supplies37 no-clause method selections; constrained
implementations and unsupported type patterns are explicitly absent.

Typed248 forwards the SAME pointer and metadata onto the selected glue, retaining
the original child return action/unwind. TypedBindingFacts.typed248_hooks checks
SpawnHooks with UntrackedDestruct selects608, rather than an empty destructor.
GenericDropMachine can execute source-resolved typed Drops beyond608 and consume
documented no-op destruction with the ordinary operand-invalidation rule.

CellDestruct504 replaces first, saves OLD T in the already reserved504 activation's
local3, initializes local0 to the carrier's unit, then drops old T before returning.
The destructor receives a reference to local3 from a SEPARATE fresh frame; its own
local3 cannot clobber the saved value. CellDestructFacts checks actual602's selected
608 witness, the source receiver/replacement implication, saved cells and holder
noninterference. DestructionNumbering uses the existing slice push/waiting_mono/
stack_mono lemmas and the existing local-write counter lemma. No counter equality
is imposed across a callee/row boundary. Pending inside a destructor does not
re-enter the504 replacement. These are local graphs, not completed arbitrary-T
source adequacy or an actual-entry caller proof.

The six exact accepted-emission bodies486/584/608/661/405/222 now have typed
instantiation. This preserves payload and allocator types in normal and cleanup
calls; wrong arity returns none. The raw LLBC has opaque405 while the accepted
amended native emission supplies structured precise glue405; both facts are
retained in METADATA_PROVENANCE.json. Emission syntax is not new binary/source
refinement evidence.

## Cleanup Match gap replaced without dropping cleanup

The unchanged pinned converter still rejects644 and454's nested cleanup Match.
The first644 pass also exposed a bound dyn type variable; it was kept bound, not
substituted with a function argument. Both failed conversion records are retained.

The NEW lowering converts only native-cleanup Match into a switch on a COPY of the
same place. Private keys use the existing Control.variant decoder. The invalid
key precedes all ordinary variant arms. A missing variant/invalid tag selects a
private nullary whose result is undefined, never source abort. No temporary cell,
allocation, source memory write or invented byte initialization is introduced.
UnwindMatchCorrectness.selection proves exact arm selection for every value;
source_selector agrees with the old structured Match selector; gap_is_undefined
checks the one administrative gap step. On valid handled variants no gap step runs.
The generator verifies all private tags are absent from the retained emission.

LoweredBody644 and LoweredBody454 retain EVERY normal/loop/unwind branch and compile.
They MUST use UnwindMatch.carrier. UnwindReplies.full_reply proves this extension
leaves EVERY pinned native reply identical, including store updates, failures,
divergence, faults, pending, world/events and the inherited panic=abort policy.
This is selection/source-syntax support; it does not assert wrapper callback/native
source effects or a whole-function erasure theorem. No old module was overwritten.

## Checked remaining obstruction and precise limits

SpawnHooksTailGap.actual_tail checks that608's actual suffix still calls opaque
Option glue157. option_source_unbound/no_option_body show the supplied source table
has no body for157. A consumer fallback P might supply one; this job has not. No
complete nonempty SpawnHooks destruction or arbitrary-T Cell adequacy is credited.

TypedBindingFacts.arc_allocator_unbound shows the current type-driven selector
cannot reconstruct Arc's glue from its erased type alone: the retained Arc type
has one type argument; Destruct impl76/method405 require payload AND allocator.
The allocator field is literally Error("removed allocator parameter").
erased_allocator_not_noop checks this marker is not silently treated as no-op.
Direct405/486/584 bindings work for an explicit actual pair, but do not solve this
reconstruction or establish default-allocator provenance. This is a METADATA/MODEL
GAP, not a counterexample to Rust Arc destruction. The initial DestructMethods draft
is retained mathematical evidence; ExactDestructMethods supersedes its method
selection for the candidate. Neither implies full source adequacy.

SOURCE/OWNER allocation registry/backing/deallocation correspondence remains open;
so do dynamic callback/vtable destructor effects, collect4 and other opaque effects.
Accordingly Range93, f6 and OwnInit histories are not promoted through these gaps.
The requested completion is NOT achieved. Next: bind157 by its exact documented
generic destruction semantics, preserve/recover the actual allocator metadata with
source provenance, then finish the last-reference SOURCE/OWNER correspondence.

## Import surface and D991

import PV_LIB_A_StoreActionTable still exports the byte-unchanged legacy
PV_LIB_StoreActionTable.v2. StoreActionTable8 exports the PARTIAL v2TypedPrograms
and v2TypedStep. The latter keeps the OWNER base, resource environment and deferred
native phases and installs the named cleanup carrier; its local agreement is over
that SAME carrier/resolver, not an old-caller transport claim.

ZERO allocation byte images are defined in session8. Unit/ADT tags and source
locals are typed semantic values, not binary initialization images. No value is
assigned to unwritten allocation bytes. Inherited total-image theorems are NOT
re-credited or used to claim source adequacy under D991. No observational forgetting
of stale/uninitialized bytes is assumed.
