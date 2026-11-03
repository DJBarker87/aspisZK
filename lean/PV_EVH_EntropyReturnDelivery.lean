import PV_EVH_EntropyReturnComplete
import PV_EVH_EntropyMoveKeys
import PV_EVH_StackTransfer
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyReturnDelivery
open ProverRwFull
open PV_EVH_StackZero (State)
open PV_EVH_EntropyDeployedLayout (original field seed entered)
open PV_EVH_EntropyMoveKeys (ready)
open PV_EVH_EntropyCallerLayout (mask result)

def transferred [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) : State :=
  PV_EVH_StackTransfer.transfer (seed owner sp w)
    (PV_EVH_EntropyReturnLayout.returnedSeed owner sp (result sp) w)
    (PV_EVH_StackTransfer.transfer (field owner sp w)
      (PV_EVH_EntropyReturnLayout.returnedField owner sp (result sp) w)
      (PV_EVH_EntropyReturnFootprint.moved sp (ready owner sp d w)))

/-- Cleanup uses the original admitted lifetime from the entry state, not
a fresh key recomputed from the post-fill state. The complete-return helper
is used below only for its key-independent physical memory projection. -/
def completed [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) : State :=
  PV_EVH_StackZero.drop (original owner sp w) (transferred owner sp d w)

theorem original_lookup [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (transferred owner sp d w).frame.live.find?
      (PV_EVH_StackCleanup.sameKey (original owner sp w).key) = some (original owner sp w) := by
  have hf := (PV_EVH_StackStores.frame
    (PV_EVH_EntropyReturnFootprint.stores sp (ready owner sp d w)) (ready owner sp d w)).1
  apply PV_EVH_EntropyMoveKeys.original_lookup owner sp (result sp)
    (PV_EVH_EntropyReturnFootprint.moved sp (ready owner sp d w)) w
  change (PV_EVH_StackStores.run _ _).frame.live.find? _ = _
  rw [hf]
  exact PV_EVH_EntropyMoveKeys.ready_lookup owner sp d w

theorem original_drop [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    PV_EVH_StackCleanup.drop64 (original owner sp w).key
      (transferred owner sp d w) =
    ⟨.returned (.ok ()),completed owner sp d w,PV_EVH_StackZero.emitted (original owner sp w)⟩ := by
  simp only [PV_EVH_StackCleanup.drop64,original_lookup]
  rfl

theorem completed_byte [ExternalTypes] (owner sp p : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) (hp : sp+64 ≤ p) :
    (completed owner sp d w).memory p =
      (PV_EVH_EntropyReturnFootprint.moved sp (ready owner sp d w)).memory p :=
  PV_EVH_StackZero.outside_preserved _ _ p (Or.inr hp)

/-- Every initializer/fill/copy in this physical interpretation preserves
the actual caller mask region. Native kernel correspondence is still the
retained KERNEL-WRITE obligation, not inferred from this modeled footprint. -/
theorem outside_ready [ExternalTypes] (owner sp p : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) (hp : sp+128 ≤ p) :
    (ready owner sp d w).memory p = w.memory p := by
  have ho : PV_EVH_StackAdmission.Outside (original owner sp w) p := Or.inr (by
    change sp+64 ≤ p
    omega)
  have hf : PV_EVH_StackAdmission.Outside (field owner sp w) p := Or.inr (by
    change sp+64+32 ≤ p
    omega)
  have hs : PV_EVH_StackAdmission.Outside (seed owner sp w) p := Or.inr (by
    change sp+96+32 ≤ p
    omega)
  unfold ready PV_EVH_EntropyPhysicalCopy.copies
  rw [PV_EVH_StackCopy.outside _ _ _ _ p hs,
    PV_EVH_StackCopy.outside _ _ _ _ p hf]
  change (PV_EVH_StackAdmission.write (seed owner sp w) _
    (PV_EVH_StackAdmission.enter (field owner sp w) _
      (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w)))).memory p = _
  rw [PV_EVH_StackAdmission.write_outside _ _ _ p hs]
  change (PV_EVH_StackAdmission.write (field owner sp w) _
    (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w))).memory p = _
  rw [PV_EVH_StackAdmission.write_outside _ _ _ p hf]
  change (PV_EVH_StackAdmission.write (original owner sp w) _ (entered owner sp w)).memory p = _
  rw [PV_EVH_StackAdmission.write_outside _ _ _ p ho]
  exact PV_EVH_StackAdmission.write_outside _ _ w p ho

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
    let out := completed owner sp d w
    out.memory (result sp) = 0 ∧
    out.memory (result sp+1+i) = w.memory (mask sp+i) ∧
    out.memory (result sp+33+i) =
      ((PV_EVH_StackEntropyFill.encode d.buffer)[i]?.getD 0).toNat ∧
    out.memory (result sp+65+i) =
      ((PV_EVH_StackEntropyFill.encode d.buffer)[32+i]?.getD 0).toNat := by
  dsimp only
  have hp (n : Nat) : sp+64 ≤ result sp+n := by
    unfold result PV_EVH_EntropyCallerLayout.caller
    omega
  rw [completed_byte owner sp _ d w (by simpa using hp 0),
    completed_byte owner sp _ d w (by have := hp (1+i); omega),
    completed_byte owner sp _ d w (by have := hp (33+i); omega),
    completed_byte owner sp _ d w (by have := hp (65+i); omega)]
  have h := PV_EVH_EntropyReturnComplete.payload sp (ready owner sp d w) i hi
  have hm : (ready owner sp d w).memory (mask sp+i) = w.memory (mask sp+i) :=
    outside_ready owner sp _ d w (by
      unfold mask PV_EVH_EntropyCallerLayout.caller
      omega)
  refine ⟨by simpa using PV_EVH_EntropyReturnFootprint.tag_byte sp (ready owner sp d w) 0 (by omega),
    h.1.trans hm,h.2.1.trans (original_ready owner sp d w i (by omega)),?_⟩
  exact h.2.2.trans (by
    simpa only [Nat.add_assoc] using original_ready owner sp d w (32+i) (by omega))

#print axioms original_lookup
#print axioms original_drop
#print axioms completed_byte
#print axioms outside_ready
#print axioms original_ready
#print axioms returned_delivery
end PV_EVH_EntropyReturnDelivery
