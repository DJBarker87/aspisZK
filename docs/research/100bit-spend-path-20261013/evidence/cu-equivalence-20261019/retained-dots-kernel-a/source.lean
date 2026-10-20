import CuSavingsRetainedDotsMiddle
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsKernel
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsRetainedDotsBinding CuSavingsRetainedDotsTail
open CuSavingsArrayBuilder
attribute [local irreducible] newPush oldPush newFinish oldFinish newDot oldDot
variable [AspisR1CanonicalDots.Shared]

theorem remap_identity {A B : Type} (r : Result (A × B)) :
    remap (fun (value,state)=>(value,id state)) r=r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨v,s⟩;rfl

theorem middle_eq (common : Shared) (q : Slice U8) (g : G) (hg : CanonicalG g) :
    @new_dots.four_dots (newShared common) q g = @new_dots.four_dots (oldShared common) q g := by
  let newInst := @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (newShared common)
  let oldInst := @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (oldShared common)
  let invariant := fun (state : new_dots.four_dots.closure)=>CanonicalG state.2
  have hcall : ∀ state index,invariant state→index.val<(4#usize).val→
      remap (fun (value,state)=>(value,id state)) (newInst.call_mut state index)=
        oldInst.call_mut (id state) index := by
    intro state index hi _
    rcases state with ⟨bytes,gamma⟩
    change remap (fun (value,state)=>(value,id state))
        (@new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
          (newShared common) (bytes,gamma) index)=
      @new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (oldShared common) (bytes,gamma) index
    rw [remap_identity]
    exact CuSavingsRetainedDotsMiddle.slot_eq common bytes gamma hi index
  have hstate : ∀ state index value after,invariant state→index.val<(4#usize).val→
      newInst.call_mut state index=.ok (value,after)→invariant after := by
    intro state index value after hi _ hs
    have hc := @CuSavingsRetainedCompositionPrefixSlotPost.source_capture (newShared common) state index
    have he := hc (value,after) hs
    change after=state at he
    rw [he]
    exact hi
  unfold new_dots.four_dots
  exact CuSavingsArrayBuilderBounded.build_naturality newInst oldInst id invariant 4#usize
    hcall hstate (q,g) hg

theorem combined_eq (common : Shared) (q : Slice U8) (h : 608≤q.val.length)
    (g : G) (hg : CanonicalG g) :
    @prefix_new_dots.four_dots (newShared common) q g =
      @old_dots.four_dots (oldShared common) q g := by
  exact (@CuSavingsRetainedCompositionPrefixPrefixKernel.source_eq (newShared common) q h g).trans
    ((middle_eq common q g hg).trans
      (congrFun (congrFun (@CuSavingsRetainedCompositionDelayedCandidate4.kernel_equivalence (oldShared common)) q) g))

#print axioms middle_eq
#print axioms combined_eq
end AspisR1.CuSavingsRetainedDotsKernel
