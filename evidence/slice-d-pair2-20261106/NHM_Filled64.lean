import NHM_FilledFrame
import NHI_WordEncoding
set_option autoImplicit false
namespace NHM_Filled64
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel
abbrev Word := NHI_WordEncoding.Word

def encode (v : alloc.vec.Vec NQ) : alloc.vec.Vec Word :=
 ⟨v.val.map NHI_WordEncoding.words,by simpa only [List.length_map] using v.property⟩

def reply : core.result.Result (alloc.vec.Vec NQ) FIo_Native.aspis_core.r0.Error →
 core.result.Result (alloc.vec.Vec Word) NHI_FilledRef.Error
 | .Ok v=>.Ok (encode v)
 | .Err _=>.Err .Allocation

/-- Exact SAME input encoding into the retained compiled reference, including
allocation errors. No allocator availability or caller success is a premise. -/
theorem cohort (reservation : Reservation) (value : NQ) :
 letI := FIo_Install.allocation reservation
 FIo_FieldBridge.map reply
  (FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
    64#usize value)=NHI_FilledRef.filled_ref 64#usize (NHI_WordEncoding.words value) := by
 rw [NHI_FilledModel.qm,NHI_FilledBridge.reference]
 cases reservation with
 | Err e=>rfl
 | Ok u=>
  cases u
  simp only [NHI_FilledModel.result,FIo_FieldBridge.map,bind_tc_ok,reply,
   encode,NHI_FilledModel.vector,List.map_replicate]

def cells {T : Type} (value : T) : Nat→List T
 | 0=>[]
 | n+1=>cells value n ++ [value]

theorem initialization {T : Type} (value : T) (n : Nat) :
 cells value n=List.replicate n value := by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [cells,ih,NHM_FilledFrame.grow]

/-- The same native window invariant supplies every cellsd cell, and the
arbitrary-prefix frame theorem applies at every step of this induction. -/
theorem selected {T : Type} (value : T) (n i : Nat) (bound : i<n) :
 (cells value n)[i]?=some value := by
 rw [initialization]
 simp [bound]

#print axioms cohort
#print axioms initialization
#print axioms selected
end NHM_Filled64
