import PV_LIB_SPEC_StackSize14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackCacheLaw20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12

/-- Symbolic cached-MIN law. Keep runtime parameters and the pre-world
abstract so kernel checking does not normalize the concrete original history. -/
theorem cached (p : Parameters) (w : OWNER) (n : Pointer) (nonzero : n.val ≠ 0)
    (cache : PV_LIB_SPEC_ThreadWords12.read w (p.loadBias.val+PV_LIB_SPEC_StackSize14.minimumOffset) = some n) :
    PV_LIB_SPEC_StackSize14.value p w
      [PV_THR2_KeyValues.pack PV_LIB_SPEC_Builder269.sizeKind [],
        PV_THR2_KeyValues.pack PV_LIB_SPEC_StackSize14.closureKind []] =
      some (.number (n.val-1)) := by
  unfold PV_LIB_SPEC_StackSize14.value
  simp only [ne_eq,not_true_eq_false,ite_false]
  change (do let value ← PV_LIB_SPEC_ThreadWords12.read w
               (p.loadBias.val+PV_LIB_SPEC_StackSize14.minimumOffset)
             if value.val=0 then none else some (Data.number (value.val-1))) = _
  rw [cache]
  exact if_neg nonzero

#print axioms cached
end PV_LIB_SPEC_StackCacheLaw20
