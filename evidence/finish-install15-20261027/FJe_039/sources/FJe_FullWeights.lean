import FJe_FullCalls
import FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FullWeights
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
def weights (q0 q1 q2 : NQ) : Array NQ 3#usize := Array.make 3#usize [q0,q1,q2]
/-- The three selected weights are from the SAME actual local-selector reads. -/
theorem value (l : State) (q0 q1 q2 : NQ) (hl : canonical l)
    (r0 : Array.index_usize l 1#usize=ok q0)
    (r1 : Array.index_usize l 9#usize=ok q1)
    (r2 : Array.index_usize l 10#usize=ok q2) :
    canonical (weights q0 q1 q2) ∧
      decoded (weights q0 q1 q2) ⟨0,by decide⟩=decoded l ⟨1,by decide⟩ ∧
      decoded (weights q0 q1 q2) ⟨1,by decide⟩=decoded l ⟨9,by decide⟩ ∧
      decoded (weights q0 q1 q2) ⟨2,by decide⟩=decoded l ⟨10,by decide⟩ := by
  have c0 := FIv_NativeArray.canonical l 1#usize q0 hl r0
  have c1 := FIv_NativeArray.canonical l 9#usize q1 hl r1
  have c2 := FIv_NativeArray.canonical l 10#usize q2 hl r2
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    simp only [weights,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2
  · change decode q0=_
    simpa only [show (1#usize).val=1 from rfl] using
      FIw_ArrayReadValue.read l 1#usize (by decide) q0 r0
  · change decode q1=_
    simpa only [show (9#usize).val=9 from rfl] using
      FIw_ArrayReadValue.read l 9#usize (by decide) q1 r1
  · change decode q2=_
    simpa only [show (10#usize).val=10 from rfl] using
      FIw_ArrayReadValue.read l 10#usize (by decide) q2 r2
#print axioms value
end AspisR1.FJe_FullWeights
end
