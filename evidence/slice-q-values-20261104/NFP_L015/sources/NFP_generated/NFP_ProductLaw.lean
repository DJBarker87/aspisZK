import NFM_ProductInstance
import ExtractedCurrentReducer
import ExtractedCurrentM31AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_ProductLaw
open Aeneas Aeneas.Std Result
/-- The emitted frozen field body is total with the exact natural spec. -/
theorem emitted (x y : U32) : ∃ out,
 FIo_Native.aspis_core.field.M31.mul x y = ok out ∧
 out.val=(x.val*y.val)%2147483647 ∧ out.val<2147483647 :=
 by
 obtain ⟨out,run,value,canonical⟩ := ExtractedCurrentReducer.current_mul_mod x y
 exact ⟨out,run,value,canonical⟩

def nodeCall (z : U32) : Result U32 := do
 let square ← FIo_Native.aspis_core.field.M31.mul z z
 let doubled ← FIo_Native.aspis_core.field.M31.double square
 FIo_Native.aspis_core.field.M31.sub doubled 1#u32

theorem node (z : U32) : ∃ out, nodeCall z=ok out ∧ out.val<2147483647 ∧
 out.val=(((z.val*z.val)%2147483647+(z.val*z.val)%2147483647)%2147483647+2147483647-1)%2147483647 := by
 obtain ⟨square,hs,vs,cs⟩ := emitted z z
 obtain ⟨doubled,hd,vd,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square cs cs
 obtain ⟨out,ho,vo,co⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 cd (by decide)
 refine ⟨out,?_,co,?_⟩
 · simp only [nodeCall,FIo_Native.aspis_core.field.M31.double,hs,hd,ho,bind_tc_ok]
 · simpa only [vs,vd,show (1#u32).val=1 from rfl] using vo
#print axioms emitted
#print axioms node
end AspisR1.NFP_ProductLaw
end
