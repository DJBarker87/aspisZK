# Session9 — Option binding and source/OWNER lifetime support; PARTIAL

Base a04fdc3582a. Target not yet established. All170 slot records and statuses
are unchanged; endpoint premises removed0/added0, new T fields0, row closures0.
No implementation, frozen spec, ledger, checker, row consumer or Lane B changes.

## Option157 is now bound

The retained LLBC declares opaque generic Option<T> glue157. Type17 has None0
with no fields and Some1 with one T field. OptionDestruct157 installs ONE named
documented-semantics graph for that exact function: initialize the source unit,
match the active variant, drop only Some.field0, then return. The T/witness stays
in the child Drop; resolution is delayed until Some. Unknown tags remain gaps.
The child retains normal/failure/divergence/fault/pending and source cleanup.
This is an explicit library semantics binding, NOT an allegedly extracted157
body. ProgramBindings9 installs it. StoreActionTable9.hooks_tail_bound checks
that608's ACTUAL tail is now resolved, replacing session8's missing157 binding.
This alone does not prove the payload's dynamic destructor or callback effects.

Global228 is separately interpreted by its empty-struct destruction semantics.
Its type1 has no fields/custom Drop; it is not an interpretation of the erased
allocator Error marker. The generator still reports228 OPAQUE: it emits no
invented native body; the named semantics graph lives in ProgramBindings9.
Both named facts are P/library interpretation items for Recount14, never T fields.

## Allocator recovered from source and typed metadata

The erased Arc type alone still cannot determine A; session8's diagnostic
remains valid. No blanket Arc<T>=>Global inference was introduced.
Deployed1.94.1 sync.rs from_inner calls from_inner_in(ptr,Global). Retained
f218/9167 constructs tagged Global;9170 supplies its type and value to315.
f315/11159 moves allocator ARG2 to local5;11160 moves it into Arc.field2.
The new generator preserves and specializes BOTH actual218/315 emitted bodies.
PROVENANCE.json retains exact normalized metadata, source excerpts/files and
hashes. Source-level structural provenance retains compiler preservation V370.

AllocatorProvenance reads actual field2 and recognizes ONLY the tagged empty
Global value. Unknown values, custom allocators and the erased Error marker
are missing, never assumed default/noop. ValueDestruct9 retains explicit impl
arguments; only unresolved UntrackedDestruct can use this value recovery.
GenericDropMachine9 installs it at Drop, typed248 and saved-old Cell504.
ProviderAllocator9 proves compatibility with the EXISTING provider's THREE-field
Arc and source218 allocator, imported by name. WeakAllocatorFacts9 and
WeakGuardCaller9 read &Global from the still-live Arc's field2, including on
the actual original thread carrier. No counter equality or read premise was
added to a row: these are local internal read facts awaiting run composition.

## Last-Weak source/OWNER lifetime correspondence

FreeLifetime9.old_world_unchanged checks the earlier source-only flaw: clearing
the source block alone leaves OWNER.live unchanged. This is a model gap, not a
Rust counterexample. AllocationBacking9 derives the registered place from the
source address. ProviderBacking9.same_place and successful_backing connect it
to the existing BoxNew producer's ARG1 backing and installed descriptor.
matching_free proves deallocation uses the SAME actual resource pointer.
It does not encode a source activation as a physical pointer or choose an id.

WeakOwnerFree9.step is a NEW resource-aware layer. For a selected last Weak,
it executes the source decrement once, checks actual Global/&Global provenance,
then uses the existing OWNER primitive free on the selected backing. The
primitive's explicit resources/encode channel supplies EVERY answer. Pending
retains the source block and a free phase, so retry cannot decrement again.
WeakFreeFacts9 gives exact source delivery on success and non-success cases.
FreeLifetime9 proves successful free ends OWNER live/metadata, retains historical
registry descriptors, and leaves EVERY byte of the old memory map unchanged.
Failure/divergence/fault/pending do not end the OWNER/source lifetime early;
allocator backend/errno can still advance exactly as the resource says.

BackingFrame9 preserves the backing through all framed native replies and fresh
later registrations. ThreadInitBacking9 handles actual local45 structurally:
its caller activation may be OLDER than the returned BoxNew allocation, so no
numerical activation-order or counter-equality premise is used for that case.
WeakFreeAgreement9 is ONE symbolic agreement outside new Weak sites/phases,
against the identical provenance machine/carrier/resource channel.

These are LOCAL graphs and producer/frame implications. They do not establish
full last-strong SOURCE/OWNER adequacy, arbitrary-T or nonempty-hook destruction,
nor an actual-entry corrected-machine history. The existing BoxNew registry/
pointer results are reused; NO BoxEffects total initialization result is used
or re-credited. Generic layout and source/byte correspondence remain explicit.

## Still open, in requested dependency order

1. Compose actual486/584/248/661 source runs with the new last-Weak resource
   step, deriving allocator/root/count facts from those runs. Include payload T
   destructor effects, the implicit weak guard, both counter branches, every
   delivered failure/pending, and actual source/OWNER frames. Unknown/custom
   allocator and unsupported dynamic destructor cases stay explicit gaps.
2. Finish arbitrary-T/nonempty hooks' dynamic destructor/callback effects and
   collect4/remaining wrappers. The source-syntax bodies from session8 alone
   do not close these effects.
3. Then Range93, f6 and the OwnInit corrected-machine caller histories in the
   specified dependency order. No caller is promoted through an unresolved action.

D991: ZERO new allocation byte images. Typed source aggregates are not physical
initialization claims. Free preserves the previous byte map; no zeroing,
observational forgetting, total image or new value for unwritten bytes occurs.

## Verification class

Focused host compiles only, one capped scope at a time,6G/8G/swap0/Tasks64,
Lean-M7000, standalone STREAMB_SLOTS=3 turn before each allocated attempt.
Summary #print axioms is labeled summary-based. One strict raw audit is run at
the end; see RAW_AUDIT.json and VALIDATION.json for final measured results.
Proof/elaboration failures are retained as compressed exact inputs; all repaired
runs changed source.55006 failed before elaboration because a dependency had not
passed; it produced no accepted object.55004 was only a failed local staging
validation, with no host turn/attempt. There was no infrastructure stop/refusal,
no cap increase and no ID-budget exhaustion claim. All implementation/runtime/
ELF artifacts are unchanged, so no full manifest/runtime/release replay ran.
