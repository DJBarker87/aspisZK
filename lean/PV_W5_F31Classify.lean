import PV_W5_F31Specification
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Classify
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem zero_capacity (n : Nat) (usize : n<PV_STX2_Source7CapacityScalars.modulus)
    (overflow : PV_STX2_Source7CapacityPaths.overflow n=false)
    (zero : PV_STX2_Source7CapacityPaths.bytes n=0) : n=0 := by
  have four : 4 % PV_STX2_Source7CapacityScalars.modulus=4 := by decide
  have bounded : 4*n<PV_STX2_Source7CapacityScalars.modulus := by
    have no := of_decide_eq_false overflow
    simp only [Nat.mod_eq_of_lt usize,four] at no
    omega
  have bytes : PV_STX2_Source7CapacityPaths.bytes n=4*n := by
    simp only [PV_STX2_Source7CapacityPaths.bytes,Nat.mod_eq_of_lt usize,four,Nat.mod_eq_of_lt bounded]
  rw [bytes] at zero
  omega

theorem boundary_value (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control) (s : Store Data)
    (parent : Frame) (parents : List Frame) (a n : Nat) (zeroed : Bool) (alloc : Data) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (out : Prefix OWNER PV_RJ4IDB.NativeEvent) (value : Data)
    (boundary : PV_FN_SLICE_f35.Boundary resources encode base K s parent parents a n zeroed alloc w external backend out)
    (returned : PV_W5_F59Reply.answer out.status=.returned (.ok value)) :
    PV_FN_SLICE_f35.ValuePost resources encode base K s (parent::parents) a n zeroed alloc w external backend value out.world := by
  cases out with
  | mk status post events =>
    cases status with
    | undefined site store => exact boundary.elim
    | returned result store => exact boundary.elim
    | fault f store => cases returned
    | running c =>
      change c.frame.activation=a ∧ c.callers=parent::parents ∧ _ at boundary
      cases completed : c.frame.completed with
      | none =>
        simp only [PV_W5_F59Reply.answer,completed] at returned
        cases returned
      | some result =>
        have equal : result=.ok value := Answer.returned.inj (by
          simpa only [PV_W5_F59Reply.answer,completed] using returned)
        cases equal
        simpa only [completed] using boundary.2.2

theorem value_classify (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K ctrl : Control) (s : Store Data)
    (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (value : Data) (post : OWNER) (usize : n<PV_STX2_Source7CapacityScalars.modulus)
    (valuePost : PV_FN_SLICE_f35.ValuePost resources encode base K s parents a n false
      PV_STX2_Source7GlobalClone.value w external backend value post) :
    (∃ pointer, value=PV_STX2_Source7QConstructorResult.value
      (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value)) ∨
      (PV_FN_SLICE_f31.L ctrl).variant value=some 1 := by
  dsimp only [PV_FN_SLICE_f35.ValuePost] at valuePost
  split at valuePost
  · subst value
    exact Or.inr rfl
  · rename_i arithmetic
    split at valuePost
    · rename_i zero
      have noOverflow : PV_STX2_Source7CapacityPaths.overflow n=false := by
        cases h : PV_STX2_Source7CapacityPaths.overflow n with
        | false => rfl
        | true => simp [h] at arithmetic
      have nzero := zero_capacity n usize noOverflow zero
      subst n
      exact Or.inl ⟨4,valuePost.1⟩
    · rcases valuePost with success | error
      · rcases success with ⟨pointer,_,shape,_⟩
        exact Or.inl ⟨pointer,shape⟩
      · rcases error with ⟨_,shape⟩
        rw [shape]
        exact Or.inr rfl

#print axioms zero_capacity
#print axioms boundary_value
#print axioms value_classify
end PV_W5_F31Classify

namespace PV_W5_F31Child
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem classify (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects)
    (value : Data)
    (returned : (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer=
      .returned (.ok value)) :
    (∃ pointer, value=PV_STX2_Source7QConstructorResult.value
      (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value)) ∨
      (PV_FN_SLICE_f31.L ctrl).variant value=some 1 := by
  have child := instantiated resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have vp := PV_W5_F31Classify.boundary_value resources encode base (PV_FN_SLICE_f31.L ctrl)
    (entered s (parent::parents) a n).store (PV_W5_F31Child.parent s (parent::parents) a n) (parent::parents)
    s.nextActivation n false PV_STX2_Source7GlobalClone.value w external backend
    (outcome resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w external backend).2 value
    child.2.2.1 returned
  exact PV_W5_F31Classify.value_classify resources encode base (PV_FN_SLICE_f31.L ctrl) ctrl _ _ _ _ w
    external backend value _ pre.usize vp

#print classify
#print axioms classify
end PV_W5_F31Child
