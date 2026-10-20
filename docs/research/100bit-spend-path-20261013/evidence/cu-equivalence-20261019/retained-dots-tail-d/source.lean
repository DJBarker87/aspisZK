import CuSavingsRetainedDotsBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1RetainedDots
open CuSavingsRetainedDotsBinding
attribute [local irreducible] newPush oldPush newFinish oldFinish newDot oldDot
abbrev G := Array E 29#usize
abbrev Range := core.ops.range.Range Usize
def CanonicalG (g : G) : Prop := ∀ i value,Array.index_usize g i=.ok value →
  CuSavingsCanonicalDotsField.WideCanonical (toE value)
variable [AspisR1CanonicalDots.Shared]

theorem body_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g)
    (slot : Usize) (iter : Range) (state : Dot) :
    @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
      (newShared common) q g slot iter state =
    @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
      (oldShared common) q g slot iter state := by
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
  apply (bind_eq_iff _ _ _).mpr
  intro entry _
  rcases entry with ⟨entry,after⟩
  simp only [uncurry_apply_pair] at *
  cases entry with
  | none => rfl
  | some term =>
    simp only [uncurry_apply_pair,bind_assoc_eq]
    apply (bind_eq_iff _ _ _).mpr
    intro a0 _
    apply (bind_eq_iff _ _ _).mpr
    intro a1 _
    apply (bind_eq_iff _ _ _).mpr
    intro a2 _
    apply (bind_eq_iff _ _ _).mpr
    intro a3 _
    apply (bind_eq_iff _ _ _).mpr
    intro a4 _
    apply (bind_eq_iff _ _ _).mpr
    intro value hread
    have hc := hg _ value hread
    apply (bind_eq_iff _ _ _).mpr
    intro a5 _
    apply (bind_eq_iff _ _ _).mpr
    intro a6 _
    apply (bind_eq_iff _ _ _).mpr
    intro a7 _
    apply (bind_eq_iff _ _ _).mpr
    intro scalar _
    change (do let (r,tail)←newPush state value scalar
               core.result.Result.unwrap core.fmt.DebugUnit r
               .ok (ControlFlow.cont (after,tail) : ControlFlow (Range × Dot) Dot)) =
      (do let (r,tail)←oldPush state value scalar
          core.result.Result.unwrap core.fmt.DebugUnit r
          .ok (ControlFlow.cont (after,tail) : ControlFlow (Range × Dot) Dot))
    rw [push_equivalence state value scalar hc]
    rfl

theorem loop_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g)
    (slot : Usize) (iter : Range) (state : Dot) :
    @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      (newShared common) iter q g slot state =
    @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      (oldShared common) iter q g slot state := by
  have he : (fun (s : Range × Dot)=>
      @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
        (newShared common) q g slot s.1 s.2) =
    (fun (s : Range × Dot)=>
      @old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
        (oldShared common) q g slot s.1 s.2) := by
    funext s
    exact body_eq common q g hg slot s.1 s.2
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
  rw [he]

#print axioms body_eq
#print axioms loop_eq
end AspisR1.CuSavingsRetainedDotsTail
