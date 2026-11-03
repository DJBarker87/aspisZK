import PV_EVH_EntropyReturnComplete
import PV_EVH_EntropyMoveKeys
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyReturnDelivery
open ProverRwFull
open PV_EVH_StackZero (State)
open PV_EVH_EntropyDeployedLayout (original field seed entered)
open PV_EVH_EntropyMoveKeys (ready)
open PV_EVH_EntropyCallerLayout (mask result)

/-- Both initializers and copies preserve original64 in the SAME delivered
state. This supplies the original register reloads; no per-lane answer is
assumed. Actual invocation/kernel interpretation remains FRAME/KERNEL P. -/
theorem original_ready [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) (i : Nat) (hi : i < 64) :
    (ready owner sp d w).memory (sp+i) =
      ((PV_EVH_StackEntropyFill.encode d.buffer)[i]?.getD 0).toNat := by
  have h := PV_EVH_EntropyDeployedLayout.separation owner sp w
  exact (PV_EVH_EntropyPhysicalCopy.original_preserved
    (original owner sp w) (field owner sp w) (seed owner sp w)
    _ h.1 h.2.1 i hi).trans
    ((PV_EVH_EntropyPhysicalCopy.admit_pair_original
      (original owner sp w) (field owner sp w) (seed owner sp w)
      _ h.1 h.2.1 i hi).trans
      (PV_EVH_StackEntropyFill.physical_buffer (original owner sp w) d
        (entered owner sp w) i hi))

/-- The complete physical returned payload is now tied to the SAME original
delivery as the source tests, rather than two supplied copy/helper answers.
The mask is read from the reached input memory; binding that memory to the
source mask and installing ownership/L3 events remain explicit P. -/
theorem returned_delivery [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) (i : Nat) (hi : i < 32) :
    let v := ready owner sp d w
    let out := PV_EVH_EntropyReturnComplete.finish owner sp v
    out.memory (result sp) = 0 ∧
    out.memory (result sp+1+i) = v.memory (mask sp+i) ∧
    out.memory (result sp+33+i) =
      ((PV_EVH_StackEntropyFill.encode d.buffer)[i]?.getD 0).toNat ∧
    out.memory (result sp+65+i) =
      ((PV_EVH_StackEntropyFill.encode d.buffer)[32+i]?.getD 0).toNat := by
  dsimp only
  have h := PV_EVH_EntropyReturnComplete.returned owner sp (ready owner sp d w) i hi
  refine ⟨h.1,h.2.1,h.2.2.1.trans (original_ready owner sp d w i (by omega)),?_⟩
  exact h.2.2.2.trans (by
    simpa only [Nat.add_assoc] using original_ready owner sp d w (32+i) (by omega))

#print axioms original_ready
#print axioms returned_delivery
end PV_EVH_EntropyReturnDelivery
