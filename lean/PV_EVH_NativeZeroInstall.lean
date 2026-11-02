import PV_EVH_NativeZeroBoundary
import PV_EVH_DeployedZeroSelected
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeZeroInstall
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_DeployedZeroSelected

/-- Concrete byte scalar dictionary selected by the deployed 1.9.0 law,
transported through the unchanged actual native selector. -/
theorem byte_dictionary (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (selected ops)
    zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes = byteZero := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (selected ops)
  change (⟨fun x => (opsNative base heap box (selected ops)).op123
    U8.Insts.ZeroizeDefaultIsZeroes x⟩ : zeroize.Zeroize U8) = byteZero
  rw [PV_EVH_NativeZeroBoundary.scalar_residual]
  rfl

/-- Actual emitted array dictionary at opsNative with the recorded residual
zeroize selection. Pinning the whole residual family at the entry remains open. -/
theorem array_value_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (selected ops)
    ∀ (n : Usize) (a : Array U8 n),
      (Array.Insts.ZeroizeZeroize n
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a =
      .ok (Array.repeat n 0#u8) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (selected ops)
  intro n a
  rw [PV_EVH_NativeZeroBoundary.emitted_array]
  rw [byte_dictionary base heap box ops]
  exact array_value a

/-- The value is restored to the caller with the deployed physical post-world,
including every write and per-element assembly barrier. No silence premise. -/
theorem execution_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (selected ops)
    ∀ {F A : Type} (n : Usize) (a : Array U8 n) (address : Nat)
      (w : PV_EVH_DeployedZeroWorld.World F)
      (caller : Array U8 n → PV_EVH_DeployedZeroWorld.World F → Result A),
      (do let value ← (Array.Insts.ZeroizeZeroize n
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a
          caller value (PV_EVH_DeployedZeroWorld.native address n.val w)) =
      caller (Array.repeat n 0#u8)
        (PV_EVH_DeployedZeroWorld.indexed address 0 n.val w) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (selected ops)
  intro F A n a address w caller
  rw [array_value_native base heap box ops]
  simp only [bind_tc_ok]
  exact PV_EVH_DeployedZeroWorld.caller_composition address n.val w
    (caller (Array.repeat n 0#u8))

#print axioms byte_dictionary
#print axioms array_value_native
#print axioms execution_native
end PV_EVH_NativeZeroInstall
