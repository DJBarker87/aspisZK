import AspisR1ProducerRelease47.SparseScan50
import R1Z.ProverCommitNativeQInverse49
import R1Z.ProverCommitSampleTail49
/-! Exact raw predicates used by the trailing-Boolean scanner and suffix.
They are related to decoded field zero/one under canonicality. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSparsePredicate50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitSubtraction47 (one one_canonical one_decode)
local instance : DecidableEq Old.Q := Classical.decEq _

def rawOne (x : Old.Q) : Bool := decide (x=one)
def rawBool (x : Old.Q) : Bool := decide (x=zero ∨ x=one)

theorem one_result (x : Old.Q) : sparse_scan50.one (ProverCommitNativeQ48.source x)=ok (rawOne x) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  by_cases ha : a=1#u32 <;> by_cases hb : b=0#u32 <;>
    by_cases hc : c=0#u32 <;> by_cases hd : d=0#u32 <;>
    simp [sparse_scan50.one,rawOne,one,ProverCommitNativeQ48.source,
      ProverCommitRelease47.convQ,ProverCommitRelease47.convC,fromQ,fromC,ha,hb,hc,hd]

theorem boolean_result (x : Old.Q) : sparse_scan50.boolean (ProverCommitNativeQ48.source x)=ok (rawBool x) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  by_cases ha0 : a=0#u32 <;> by_cases ha1 : a=1#u32 <;> by_cases hb : b=0#u32 <;>
    by_cases hc : c=0#u32 <;> by_cases hd : d=0#u32 <;>
    simp [sparse_scan50.boolean,rawBool,one,zero,ProverCommitNativeQ48.source,
      ProverCommitRelease47.convQ,ProverCommitRelease47.convC,fromQ,fromC,ha0,ha1,hb,hc,hd]

theorem one_iff (x : Old.Q) (hx : Canonical x) : rawOne x=true ↔ decode x=1 := by
  rw [rawOne,decide_eq_true_eq,←one_decode]
  exact (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff x one hx one_canonical).symm

theorem boolean_iff (x : Old.Q) (hx : Canonical x) : rawBool x=true ↔ decode x=0 ∨ decode x=1 := by
  rw [rawBool,decide_eq_true_eq]
  have hone : x=one ↔ decode x=1 := by
    rw [←one_decode]
    exact (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff x one hx one_canonical).symm
  exact or_congr (ProverCommitNativeQInverse49.zero_iff x hx).symm hone

theorem boolean_value (x : Old.Q) (hx : Canonical x) (hb : rawBool x=true) :
    decode x=if rawOne x then 1 else 0 := by
  by_cases ho : rawOne x=true
  · rw [if_pos ho];exact (one_iff x hx).mp ho
  · rw [if_neg ho]
    exact ((boolean_iff x hx).mp hb).resolve_right (fun h => ho ((one_iff x hx).mpr h))

#print axioms one_result
#print axioms boolean_result
#print axioms one_iff
#print axioms boolean_iff
#print axioms boolean_value
end R1Z.ProverCommitSparsePredicate50
