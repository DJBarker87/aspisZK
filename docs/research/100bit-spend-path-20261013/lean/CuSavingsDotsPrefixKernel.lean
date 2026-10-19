import CuSavingsArrayBuilderBounded
import CuSavingsDotsSlotPost
import CuSavingsDotsSlotPrefix
import CuSavingsDotsSameBytes

/-! Complete emitted old/new kernel comparison on every sufficiently long
query slice. The constructor proves its own four-slot bound and stable
capture invariant. Shared arithmetic remains universally quantified; the
concrete array builder's Rust-library admission is an explicit later boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsDotsPrefixKernel
open Aeneas Aeneas.Std Result AspisR1CuDots
open CuSavingsArrayBuilder CuSavingsPrefix

def replaceBytes (bytes : Slice U8) (state : old_dots.four_dots.closure) :
    old_dots.four_dots.closure := (bytes,state.2)

def HasPrefix (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (state : old_dots.four_dots.closure) : Prop :=
  state.1 = (prefixArray bytes h).to_slice

variable [Arithmetic]

theorem callback_transport (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (hs : slot.val < 4) :
    remap (fun (value,state1) => (value,replaceBytes bytes state1))
      (old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        ((prefixArray bytes h).to_slice,gamma) slot) =
      old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (bytes,gamma) slot := by
  rw [CuSavingsDotsSlot.old_factor,CuSavingsDotsSlot.old_factor]
  exact (CuSavingsDotsSlot.naturality _ _ _ _ _).trans
    ((CuSavingsDotsSlotPrefix.source_eq bytes h gamma slot hs _).trans (by rfl))

theorem old_prefix (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) :
    old_dots.four_dots (prefixArray bytes h).to_slice gamma =
      old_dots.four_dots bytes gamma := by
  have hcall : ∀ state index, HasPrefix bytes h state → index.val < (4#usize).val →
      remap (fun (value,state1) => (value,replaceBytes bytes state1))
        (old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
          state index) =
        old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
          (replaceBytes bytes state) index := by
    intro state index hi hindex
    rcases state with ⟨captured,g⟩
    change captured = (prefixArray bytes h).to_slice at hi
    cases hi
    have h4 : (4#usize).val = 4 := by scalar_tac
    exact callback_transport bytes h g index (by simpa only [h4] using hindex)
  have hstate : ∀ state index value state1,
      HasPrefix bytes h state → index.val < (4#usize).val →
      old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        state index = .ok (value,state1) → HasPrefix bytes h state1 := by
    intro state index value state1 hi hindex hc
    have hs : state1 = state := CuSavingsDotsSlotPost.source_capture state index (value,state1) hc
    rw [hs]
    exact hi
  unfold old_dots.four_dots
  exact CuSavingsArrayBuilderBounded.build_naturality
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    (replaceBytes bytes) (HasPrefix bytes h) 4#usize hcall hstate
    ((prefixArray bytes h).to_slice,gamma) rfl

theorem optimized_expansion (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) :
    new_dots.four_dots bytes gamma =
      core.array.from_fn 4#usize
        new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (prefixArray bytes h,gamma) := by
  have expand : new_dots.four_dots bytes gamma =
      (do let fixed ← AspisR1CuPrefix.fixed_prefix bytes
          core.array.from_fn 4#usize
            new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
            (fixed,gamma)) := by
    simp only [new_dots.four_dots,AspisR1CuPrefix.fixed_prefix,bind_assoc_eq]
  rw [expand,CuSavingsPrefix.source_success bytes h]
  rfl

theorem source_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) :
    new_dots.four_dots bytes gamma = old_dots.four_dots bytes gamma := by
  exact (optimized_expansion bytes h gamma).trans
    ((CuSavingsDotsSameBytes.construct_same (prefixArray bytes h,gamma)).trans
      (old_prefix bytes h gamma))

theorem query_composition (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (gamma : Array field.wide_exact.WideExact 29#usize) :
    (do let bytes ← AspisR1CuQuery.verifier.View.query view index
        new_dots.four_dots bytes gamma) =
      (do let bytes ← AspisR1CuQuery.verifier.View.query view index
          old_dots.four_dots bytes gamma) := by
  apply (bind_eq_iff (AspisR1CuQuery.verifier.View.query view index) _ _).mpr
  intro bytes hquery
  exact source_eq bytes (CuSavingsQueryAccess.query_prefix_bound view index bytes hquery) gamma

#print axioms callback_transport
#print axioms old_prefix
#print axioms optimized_expansion
#print axioms source_eq
#print axioms query_composition
end AspisR1.CuSavingsDotsPrefixKernel
