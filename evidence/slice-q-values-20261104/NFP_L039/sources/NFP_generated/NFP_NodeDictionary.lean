import NFP_ProductLaw
import ExtractedCurrentReducer
import ExtractedCurrentM31AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_NodeDictionary
open Aeneas Aeneas.Std Result

theorem product (x y : U32) :
 FIo_Native.aspis_core.field.M31.mul x y = AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
 obtain ⟨a,ha,va,ca⟩ := NFP_ProductLaw.emitted x y
 obtain ⟨b,hb,vb,cb⟩ := ExtractedCurrentReducer.current_mul_mod x y
 have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
 rw [ha,hb,same]

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 FIo_Native.aspis_core.field.M31.add x y = AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
 obtain ⟨a,ha,va,ca⟩ := NFP_NatBase.add x y hx hy
 obtain ⟨b,hb,vb,cb⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
 have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
 rw [ha,hb,same]

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 FIo_Native.aspis_core.field.M31.sub x y = AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
 obtain ⟨a,ha,va,ca⟩ := NFP_NatBase.sub x y hx hy
 obtain ⟨b,hb,vb,cb⟩ := ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
 have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
 rw [ha,hb,same]

def probeNode (z : U32) : Result U32 := do
 let square ← AspisR1Qm31ArithmeticProbe.field.M31.mul z z
 let doubled ← AspisR1Qm31ArithmeticProbe.field.M31.double square
 AspisR1Qm31ArithmeticProbe.field.M31.sub doubled 1#u32

theorem node (z : U32) : NFP_ProductLaw.nodeCall z = probeNode z := by
 obtain ⟨square,hs,vs,cs⟩ := NFP_ProductLaw.emitted z z
 obtain ⟨doubled,hd,vd,cd⟩ := NFP_NatBase.add square square cs cs
 unfold NFP_ProductLaw.nodeCall probeNode
 rw [←product,hs]
 simp only [bind_tc_ok,FIo_Native.aspis_core.field.M31.double,
  AspisR1Qm31ArithmeticProbe.field.M31.double]
 rw [←add square square cs cs,hd]
 simp only [bind_tc_ok]
 exact sub doubled 1#u32 cd (by decide)
#print axioms product
#print axioms add
#print axioms sub
#print axioms node
end AspisR1.NFP_NodeDictionary
end
