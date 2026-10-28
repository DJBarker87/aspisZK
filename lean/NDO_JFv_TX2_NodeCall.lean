import NDO_JFv_TX2_LineCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_NodeCall
open Aeneas Aeneas.Std Result

def sourceCall (x : U32) : Result U32 := do
  let s ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
  let d ← AspisR1Qm31ArithmeticProbe.field.M31.double s
  AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32

theorem source (x : U32) : ∃ z, sourceCall x=ok z ∧ z.val<2147483647 ∧
    z.val=(((x.val*x.val)%2147483647+(x.val*x.val)%2147483647)%2147483647+2147483647-1)%2147483647 := by
  obtain ⟨square,hs,vs,cs⟩ := ExtractedCurrentReducer.current_mul_mod x x
  obtain ⟨doubled,hd,vd,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  obtain ⟨z,hz,vz,cz⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 cd (by decide)
  refine ⟨z,?_,cz,?_⟩
  · simp only [sourceCall,AspisR1Qm31ArithmeticProbe.field.M31.double,hs,hd,hz,bind_tc_ok]
  · simpa only [vs,vd,show (1#u32).val=1 from rfl] using vz
#print axioms source
end AspisR1.JFv_TX2_NodeCall
end
