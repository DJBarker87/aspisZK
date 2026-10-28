import RPv_FJe_ExternalCalls
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_PackedSumTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
theorem source (p : FJe_ExternalCalls.Packed) (hp : canonical p) :
    ∃ total,FJe_ExternalCalls.sum p=ok total ∧ Canon total := by
  have zero : Canon field.QM31.ZERO := FIv_NativeValue.zero.1
  obtain ⟨q0,r0,c0⟩ := JFy_ArrayTotal.read p 0#usize (by decide) hp
  obtain ⟨q1,r1,c1⟩ := JFy_ArrayTotal.read p 1#usize (by decide) hp
  obtain ⟨q2,r2,c2⟩ := JFy_ArrayTotal.read p 2#usize (by decide) hp
  obtain ⟨q3,r3,c3⟩ := JFy_ArrayTotal.read p 3#usize (by decide) hp
  obtain ⟨s0,h0,cs0,_⟩ := FIv_PreparedTotal.add field.QM31.ZERO q0 zero c0
  obtain ⟨s1,h1,cs1,_⟩ := FIv_PreparedTotal.add s0 q1 cs0 c1
  obtain ⟨s2,h2,cs2,_⟩ := FIv_PreparedTotal.add s1 q2 cs1 c2
  obtain ⟨out,ho,co,_⟩ := FIv_PreparedTotal.add s2 q3 cs2 c3
  exact ⟨out,by simp only [FJe_ExternalCalls.sum,r0,r1,r2,r3,h0,h1,h2,ho,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_PackedSumTotal
end
