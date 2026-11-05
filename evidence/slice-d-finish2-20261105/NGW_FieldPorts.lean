import NGM_ProbeTransport
import NGM_DoubleModel
set_option autoImplicit false
namespace NGW_FieldPorts
open Aeneas Aeneas.Std Result NGM_ProbeTransport

theorem add (x y : FQ) :
 (do let z ← FIn_WeightsExtract.field.QM31.add x y;ok (toQ z))=
 FIo_Native.aspis_core.field.QM31.add (toQ x) (toQ y) := by
 simp only [FIn_WeightsExtract.field.QM31.add,FIo_Native.aspis_core.field.QM31.add,toQ]
 simp only [←cm_add,bind_assoc_eq,bind_tc_ok]

theorem sub (x y : FQ) :
 (do let z ← FIn_WeightsExtract.field.QM31.sub x y;ok (toQ z))=
 FIo_Native.aspis_core.field.QM31.sub (toQ x) (toQ y) := by
 simp only [FIn_WeightsExtract.field.QM31.sub,FIo_Native.aspis_core.field.QM31.sub,toQ]
 simp only [←cm_sub,bind_assoc_eq,bind_tc_ok]

def nativeWords (x : NQ) : Array U32 4#usize := Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
theorem words (x : FQ) : nativeWords (toQ x)=NGM_DoubleModel.words x := rfl

#print axioms add
#print axioms sub
#print axioms words
end NGW_FieldPorts
