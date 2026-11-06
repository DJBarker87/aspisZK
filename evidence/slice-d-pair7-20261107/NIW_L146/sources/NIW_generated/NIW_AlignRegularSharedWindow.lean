import NIW_AlignRegularWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularSharedWindow
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularWindow
variable [FIo_Native.Allocation]

/-- Shared-arm omitted slots remain zero at the actual full regular post,
including returned Err. The guard is split internally, not retained as a
successful-child or shared-arm precondition of a native root. -/
theorem source (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (inv : NHX_RegularPost.Inv before initial) :
 if NGM_GuardExact.guard c.w.value 2#usize then
  Slot 1 (NIW_AlignRegularPhase.run c before).2.outcome ∧ Slot 3 (NIW_AlignRegularPhase.run c before).2.outcome
 else True := by
 cases shared : NGM_GuardExact.guard c.w.value 2#usize with
 | false => trivial
 | true =>
  constructor
  · apply zero_slot c before domain c0 c1 inv 1 (by decide)
    intro k member
    simp only [NHM_RegularKinds.kinds,shared,ite_true,List.mem_cons,List.mem_singleton] at member
    rcases member with same|same|same <;> subst k <;> decide
  · apply zero_slot c before domain c0 c1 inv 3 (by decide)
    intro k member
    simp only [NHM_RegularKinds.kinds,shared,ite_true,List.mem_cons,List.mem_singleton] at member
    rcases member with same|same|same <;> subst k <;> decide

#print axioms source
end AspisR1.NIW_AlignRegularSharedWindow
