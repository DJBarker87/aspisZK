import PV_LIB_A_ScopePayloadShape14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ScopeIncrementShape14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_ScopePayloadShape14 PV_LIB_A_StorePrimitiveV2

theorem zero_increment :
    (if 0 > modulus/2-1 then 0 else (0+1)%modulus) = 1 := by
  simp only [Nat.not_lt_zero,if_false,Nat.zero_add]
  exact Nat.mod_eq_of_lt (by decide)

/-- Exact named457 source projection, with the actual ScopeData field order.
The count changes0→1 while strong/weak, main-thread and panic fields survive.
No native answer is selected and no allocation bytes are initialized. -/
theorem increment (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER) (a slot : Nat)
    (atomicKind cellKind strong weak thread panicked : Data) :
    PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 (carrier C b)
      [PV_STX2_TypedReferences.reference ⟨a,slot,[2]⟩ .null]
      (stored s a slot atomicKind cellKind strong weak thread panicked 0) w =
      some (stored s a slot atomicKind cellKind strong weak thread panicked 1) := by
  unfold PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 modifyNumber atReference
  simp only []
  rw [reference C b w a slot]
  change (numberAt (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked 0)
    (count a slot)).bind _ = _
  unfold numberAt
  rw [read_count]
  change writeAddress (carrier C b) (stored s a slot atomicKind cellKind strong weak thread panicked 0)
    (count a slot) (some (.number (if 0 > modulus/2-1 then 0 else (0+1)%modulus))) = _
  rw [zero_increment,write_count]

#print axioms zero_increment
#print axioms increment
end PV_LIB_A_ScopeIncrementShape14
