import NIG_FilledCoverage
import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_FilledClause
open Aeneas Aeneas.Std Result AspisR1 NP6_StdModel
abbrev K := AspisR1Stage2.aspis_core.field.QM31
abbrev Error := AspisR1Stage2.verifier.Error

def reserved : Reservation → Bool
 | .Ok () => true
 | .Err _ => false

def value (q : FIo_Native.aspis_core.field.QM31) : K :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def reply : core.result.Result (alloc.vec.Vec FIo_Native.aspis_core.field.QM31)
 FIo_Native.aspis_core.r0.Error → core.result.Result (alloc.vec.Vec K) Error
 | .Err _ => .Err .Allocation
 | .Ok v => .Ok ⟨v.val.map value,by simpa only [List.length_map] using v.property⟩

def native (reservation : Reservation) :=
 letI:=FIo_Install.allocation reservation
 FIo_FieldBridge.map reply
  (FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHX_FilledZero.zeroQ)

/-- Apply the CLOSED filled law to the actual zero64 arguments, preserving both
reservation arms and the complete Vec value. Reservation is the SAME primitive
outcome in both sides, not an allocator-availability or successful-output fact.
Binding that outcome to the parent's native reserve record remains separate. -/
theorem source (reservation : Reservation) :
 native reservation=
 CheckpointBytes3Allocation.filled (reserved reservation) 64#usize
  ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := by
 unfold native
 rw [NHI_FilledModel.qm,CheckpointBytes3Allocation.filled_exact]
 cases reservation with
 | Err e => rfl
 | Ok unit =>
  cases unit
  simp only [NHI_FilledModel.result,FIo_FieldBridge.map,bind_tc_ok,reply,
   NHI_FilledModel.vector,List.map_replicate,reserved,if_true]
  rfl
#print axioms source
end NJC_FilledClause
