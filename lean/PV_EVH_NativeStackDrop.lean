import PV_EVH_NativeZeroInstall
import PV_EVH_StackCleanup
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeStackDrop
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_HeapOwnership (Key)
open PV_EVH_StackZero (Slot State Cleared)
open PV_EVH_StackCleanup (sameKey drop64)

/-- Source array dispatch at the actual native selector, physical cleanup,
retired memory and retained write/barrier history in one leaf theorem.
The entry must still establish the original live stack slot (hs/hn), and use
the recorded residual source selection rather than an arbitrary dictionary. -/
theorem native_drop64 (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_DeployedZeroSelected.selected ops)
    ∀ (key : Key) (slot : Slot) (a : Array U8 64#usize) (w : State),
      w.frame.live.find? (sameKey key) = some slot → slot.initialized = 64 →
      (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a =
          .ok (Array.repeat 64#usize 0#u8) ∧
      (drop64 key w).outcome = .returned (.ok ()) ∧
      Cleared slot (drop64 key w).state ∧
      (drop64 key w).state.frame.runtime = w.frame.runtime ∧
      (drop64 key w).state.frame.retired = slot :: w.frame.retired ∧
      (drop64 key w).state.history = w.history ++
        (PV_EVH_ZeroizeArray.events slot.key 0 slot.initialized).map
          (PV_EVH_ZeroAddressBridge.physical slot.address) ∧
      (drop64 key w).events = PV_EVH_StackZero.emitted slot := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_DeployedZeroSelected.selected ops)
  intro key slot a w hs hn
  refine ⟨PV_EVH_NativeZeroInstall.array_value_native base heap box ops 64#usize a,?_⟩
  have hd : drop64 key w =
      ⟨.returned (.ok ()),PV_EVH_StackZero.drop slot w,PV_EVH_StackZero.emitted slot⟩ := by
    simp only [drop64,hs,hn,if_true]
  rw [hd]
  exact ⟨rfl,PV_EVH_StackZero.dropped_cleared slot w,
    PV_EVH_StackZero.dropped_runtime slot w,PV_EVH_StackZero.retired_after_drop slot w,
    PV_EVH_StackZero.dropped_history slot w,rfl⟩

#print axioms native_drop64
end PV_EVH_NativeStackDrop
