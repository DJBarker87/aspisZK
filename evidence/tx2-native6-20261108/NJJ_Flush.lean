import NJJ_Value
set_option autoImplicit false
noncomputable section
namespace NJJ_Flush
open Aeneas Aeneas.Std Result AspisR1
abbrev K := VTop_Stages.aspis_core.field.QM31

def cell (row : S8OwnedP6ValueModel.Row) : K :=
 Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish
  (S8OwnedP6Finish.modelValue row))

def output (b : VTop_Stages.verifier.BatchedWeights) : Slice K :=
 ⟨b.raw.val.map cell,by simpa only [List.length_map] using b.raw.property⟩

/-- Complete source Result and all64 mutable destination cells after the
native arbitrary-step/value/end cuts, with no value-success premise and no
bound on the U64 raw lanes. The dimensions are derived caller invariants. -/
theorem source (b : VTop_Stages.verifier.BatchedWeights) (old : Slice K)
 (rawSize : b.raw.val.length=64) (oldSize : old.val.length=64) :
 Port3_FlushInstall.flush b old=ok (output b) := by
 rw [Port3_FlushInstall.flush_exact b old (by omega)]
 apply congrArg Result.ok
 apply Subtype.ext
 simp only [Port3_FlushInstall.fromSlice,S8JoinFinishExact.output,
  Port3_FlushInstall.toWeights,alloc.vec.Vec.length,List.length_map,List.map_map]
 rw [List.take_of_length_le (by omega)]
 rfl

theorem canonical (b : VTop_Stages.verifier.BatchedWeights) :
 ∀ q∈(output b).val,Port3_FlushInstall.Canonical q := by
 intro q member
 obtain ⟨row,_,same⟩ := List.mem_map.mp member
 subst q
 exact Port3_FlushInstall.model_canonical row

#print axioms source
#print axioms canonical
end NJJ_Flush
