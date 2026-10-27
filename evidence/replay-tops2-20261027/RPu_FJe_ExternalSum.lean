import RPu_FJe_ExternalCalls
import RPu_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ExternalSum
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJe_ExternalCalls (Packed)
def model (p : Packed) :=
  (((0+decoded p ⟨0,by decide⟩)+decoded p ⟨1,by decide⟩)+
    decoded p ⟨2,by decide⟩)+decoded p ⟨3,by decide⟩
/-- The actual ordered four-way sum on the SAME returned local packed array. -/
theorem value (p : Packed) (out : NQ) (hp : canonical p)
    (run : FJe_ExternalCalls.sum p=ok out) : Canon out ∧ decode out=model p := by
  unfold FJe_ExternalCalls.sum at run
  obtain ⟨q0,r0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s0,rs0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q1,r1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s1,rs1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q2,r2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s2,rs2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q3,r3,run⟩ := FIv_Map.bind_success _ _ _ run
  have v0 := FIv_NativeValue.add _ _ _ FIv_NativeValue.zero.1
    (FIv_NativeArray.canonical p 0#usize q0 hp r0) rs0
  have v1 := FIv_NativeValue.add _ _ _ v0.1
    (FIv_NativeArray.canonical p 1#usize q1 hp r1) rs1
  have v2 := FIv_NativeValue.add _ _ _ v1.1
    (FIv_NativeArray.canonical p 2#usize q2 hp r2) rs2
  have v3 := FIv_NativeValue.add _ _ _ v2.1
    (FIv_NativeArray.canonical p 3#usize q3 hp r3) run
  refine ⟨v3.1,?_⟩
  rw [v3.2,v2.2,v1.2,v0.2,FIv_NativeValue.zero.2,
    FIw_ArrayReadValue.read p 0#usize (by decide) q0 r0,
    FIw_ArrayReadValue.read p 1#usize (by decide) q1 r1,
    FIw_ArrayReadValue.read p 2#usize (by decide) q2 r2,
    FIw_ArrayReadValue.read p 3#usize (by decide) q3 r3]
  rfl
#print axioms value
end AspisR1.FJe_ExternalSum
end
