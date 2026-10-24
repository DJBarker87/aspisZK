# Port25ARRAY exact interface and status

Port23 candidate remains UNMERGED/UNADOPTED. No installed premise changed.

Before (unchanged raw external template):

```
Array T N → Result (IterMut T × (IterMut T → Array T N))
```

Actual unchanged caller: `back : IterMut U64 → IterMut U64`, followed by
`into_iter_back back`. The template still cannot typecheck this application.

After (new content composition, no backend registration or external axiom):

```
Port25ARRAY.arrayIntoIter :
  Array T N → Result (IterMut T × ((IterMut T → IterMut T) → Array T N))
```

Its implementation is exactly:

```
let (s,arrayBack) ← lift (Array.to_slice_mut a)
let (it,sliceBack) ← core.slice.Slice.iter_mut s
ok (it,fun f => arrayBack (sliceBack (f it)))
```

Literal inherited native source: array/mod.rs:376-378 says
`fn into_iter(self) -> IterMut<'a,T> { self.iter_mut() }`;
slice/mod.rs:1061-1063 delegates to `IterMut::new(self)`. Complete selected
bodies and file hashes are in source-assessment.json, reused from the pinned
Port23 graph. No new native/sysroot/SBF identity validation is attributed.

`delegation` proves this composition returns the original content iterator
and `fun f => Array.from_slice a (f original).slice`. `back_carrier` proves
its entire list is the transformed slice when its length is N, otherwise the
original list, retaining the existing wrapper's fallback for malformed f.
`back_identity` proves identity readback recovers the entire original array.
No assumed equality, length premise, canonicality or chosen native instance
appears in these statements. `concrete` specializes to the exact U64[4] ABI.
This is a concrete derivation from existing approved pure collection content
wrappers; it is not an interpretation of unsafe pointer internals. No D157
TrustedStd field, unsafe/panic/allocator policy, or trust assumption is added.

The source-refinement gap is explicit: the raw generated caller/template are
still ill-typed together. The new content composition has not been associated
with that missing external by a validated compiler/backend interface, nor has
its native ordered primitive-effect interpretation been produced. Instantiating
the Port23 parameter with `concrete` would not discharge those obligations.

# Scalar and owned-row work

`fold_total` proves the exact mask/shift/add fold succeeds on EVERY full U64.
`product_total` proves the widening product succeeds for EVERY pair of full
U32 words. `scalar_all_results` rewrites the actual existing S7 scalar to a
checked `addWord` followed by the total pure `finish`. Raw overflow remains
in `addWord`; fail and div are retained. No safe-domain premise was added.
`folded` is Classical.choose of a proved successful exact fold, not an assumed
fold function. All its dependencies are standard axioms.

Failed final audit individually elaborated `owned_four` with standard axioms:
the exact existing S7 owned four-lane row equals four ordered checked adds,
then the four pure finishes. It used the complete four-word carrier `toK`.
That module exited 1, so this declaration is NOT promoted as a successfully
compiled bridge. The full source/statement/axioms remain in lean-007.

# Actual loop failures, not mathematical counterexamples

lean-004: direct rfl did not establish Range.next or generic loop unrolling;
the initial congruence also encountered nested ControlFlow/Result structure.
lean-005: Result has no synthesized Decidable equality for the attempted tiny
`decide` checks; cases did not rewrite the left loop match. No decision result
was accepted and no resource failure occurred.
lean-006: symbolic Range.next and generic add_unroll succeeded individually;
the stopped-range omega call failed to normalize projections. The four-step
proof failed before normalization of tuple lets and nested Result binds.
lean-007: `owned_four` succeeded individually. `fold_body_complete` failed only
with displayed tuple-let equalities remaining in its none/some cases. The
actual full add loop, full fold loop and mutable/owned row equality were NOT
established. This is an elaboration/budget frontier, not evidence of falsity.
All failed source drafts and complete diagnostics are retained. No failed
module is imported by the two successfully compiled new source modules.

# Consumers and security frontier

The full actual raw Vec/terms/index/power join remains open. No safety domain
is assumed or claimed to follow from a reached caller. No old Kani/domain
receipt is reassigned to this producer. No Kani or extraction rerun occurred.

Actual source query effects need a separately justified fixed primitive
interpretation and ordered rejected-prefix association. NoHash does not follow
from carrier/Result/output equality. Full op6 four_dots, geometry, line/circle,
accumulator, trace and observer composition remain open. Port17RELEASE_Invariant
proves CallsIn on actual release calls starting with None; it is reused only
in that scope and supplies no arbitrary Some-to-None retargeting. No whole
heap-allocation prerequisite is imposed on this local nonallocating join.
Both deployed security targets remain not yet established.
