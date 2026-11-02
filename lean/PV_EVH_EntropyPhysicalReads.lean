import PV_EVH_EntropyCopiedRead
import PV_EVH_EntropyPhysicalCopy
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyPhysicalReads
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackRegions (Separate)

/-- Both checked source array reads agree with the physical halves
copied from a delivered buffer. Neither source-read answer is a premise.
Reaching this copy state is the success-only source continuation obligation;
NativeEntropyPhysical separately retains its completed-fill guard. Physical
read/copy observations and actual frame interpretation remain P. -/
theorem from_delivery [ExternalTypes] (original field seed : Slot)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State)
    (ho : original.initialized = 64) (hf : field.initialized = 32)
    (hs : seed.initialized = 32)
    (hfo : Separate field original) (hso : Separate seed original)
    (hsf : Separate seed field) (i : Usize) (hi : i.val < 32) :
    let v := PV_EVH_EntropyPhysicalCopy.copies original field seed
      (PV_EVH_EntropyPhysicalCopy.admit_pair field seed
        (PV_EVH_StackEntropyFill.post original d w))
    ∃ x y, Array.index_usize (PV_EVH_EntropyHalves.field d.buffer) i = .ok x ∧
      Array.index_usize (PV_EVH_EntropyHalves.seed d.buffer) i = .ok y ∧
      v.memory (field.address+i.val) = x.val ∧
      v.memory (seed.address+i.val) = y.val := by
  dsimp only
  have h := PV_EVH_EntropyPhysicalCopy.delivered_halves original field seed
    (PV_EVH_StackEntropyFill.post original d w) d.buffer ho hf hs hfo hso hsf
    (fun j hj => PV_EVH_StackEntropyFill.physical_buffer original d w j (by omega))
  obtain ⟨x,hx,hxm⟩ := PV_EVH_EntropyCopiedRead.first_read d.buffer i _ field.address hi (h.1 i.val hi)
  obtain ⟨y,hy,hym⟩ := PV_EVH_EntropyCopiedRead.second_read d.buffer i _ seed.address hi (h.2 i.val hi)
  exact ⟨x,y,hx,hy,hxm,hym⟩

#print axioms from_delivery
end PV_EVH_EntropyPhysicalReads
