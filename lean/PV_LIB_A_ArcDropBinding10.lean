import PV_LIB_A_StoreActionTable10
set_option autoImplicit false
namespace PV_LIB_A_ArcDropBinding10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Tie the saved return destination in ArcDropCompare10.wait back to21732. -/
theorem actual_count_destination (types : List Data) :
    ∃ site operands,
      PV_LIB_A_TypedBody486.node13 types = .leaf (.call site
        PV_LIB_A_ArcDropCompare10.call.1 operands (.local 3)
        PV_LIB_A_ArcDropCompare10.call.2) := ⟨_,_,rfl⟩

/-- The checked comparison destination and branch operand are the same local2. -/
theorem actual_comparison_destination (types : List Data) :
    ∃ site expression,
      PV_LIB_A_TypedBody486.node16 types = .leaf (.bind site (.local 2) expression) := ⟨_,_,rfl⟩

/-- Local value obstruction that motivated the new581 interpretation: a
source subtraction alone does not make an arbitrary native payload the old
count. This records a model gap, not a counterexample to shipped Rust. -/
theorem corrected_old_one (w : PV_EVHB_OwnerMachine.OWNER) (events : List PV_RJ4IDB.NativeEvent) :
    PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581 1
      ⟨.returned (.ok (.number 2)),w,events⟩ =
      ⟨.returned (.ok (.number 1)),w,events⟩ ∧
    decide ((1 : Nat) ≠ 1) = false ∧ decide ((2 : Nat) ≠ 1) = true := ⟨rfl,rfl,rfl⟩

#print axioms actual_count_destination
#print axioms actual_comparison_destination
#print axioms corrected_old_one
end PV_LIB_A_ArcDropBinding10
