import CuSavingsRetainedDotsSuffix
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsMiddle
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsRetainedDotsBinding CuSavingsRetainedDotsTail
attribute [local irreducible] newPush oldPush newFinish oldFinish newDot oldDot
variable [AspisR1CanonicalDots.Shared]

def raw (common : Shared) (q : Slice U8) (g : G) (slot : Usize) : Result (E × (Slice U8 × G)) := do
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    ({start:=0#usize,«end»:=26#usize} : core.ops.range.Range Usize) 4#usize
  let limbs ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
    iter q g slot (Array.repeat 8#usize 0#u64)
  let coefficients ← core.array.from_fn 8#usize
    new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 limbs
  CuSavingsRetainedDotsSuffix.raw common q g slot coefficients

theorem source_factor (common : Shared) (q : Slice U8) (g : G) (slot : Usize) :
    @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut common (q,g) slot =
      raw common q g slot := by
  exact (@CuSavingsRetainedCompositionDelayedKernel.new_factor common (q,g) slot).trans (by rfl)

theorem raw_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g) (slot : Usize) :
    raw (newShared common) q g slot=raw (oldShared common) q g slot := by
  unfold raw
  apply (bind_eq_iff _ _ _).mpr
  intro iter _
  apply (bind_eq_iff _ _ _).mpr
  intro limbs _
  apply (bind_eq_iff _ _ _).mpr
  intro coefficients _
  exact CuSavingsRetainedDotsSuffix.source_eq common q g hg slot coefficients

theorem slot_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g) (slot : Usize) :
    @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (newShared common) (q,g) slot =
    @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (oldShared common) (q,g) slot :=
  (source_factor (newShared common) q g slot).trans
    ((raw_eq common q g hg slot).trans (source_factor (oldShared common) q g slot).symm)

#print axioms source_factor
#print axioms raw_eq
#print axioms slot_eq
end AspisR1.CuSavingsRetainedDotsMiddle
