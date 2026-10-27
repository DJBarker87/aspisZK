import XRq_ComplexSub
import XRp_PowersQAdd
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRp_PowersComplex XRp_PowersQAdd
set_option autoImplicit false
noncomputable section
namespace XRq_QmSub

theorem sub (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 mapR toQ (XRn_Join_Field.field.QM31.sub a b) =
 AspisR1CurrentWideMul.field.QM31.sub (toQ a) (toQ b) := by
 unfold XRn_Join_Field.field.QM31.sub AspisR1CurrentWideMul.field.QM31.sub
   AspisR1Qm31ArithmeticProbe.field.QM31.sub
 change mapR toQ (do
   let x ← XRn_Join_Field.field.CM31.sub a.c0 b.c0
   let y ← XRn_Join_Field.field.CM31.sub a.c1 b.c1
   ok (⟨x,y⟩ : EQ)) = (do
     let x ← AspisR1Qm31ArithmeticProbe.field.CM31.sub (toC a.c0) (toC b.c0)
     let y ← AspisR1Qm31ArithmeticProbe.field.CM31.sub (toC a.c1) (toC b.c1)
     ok (⟨x,y⟩ : TQ))
 rw [←XRq_ComplexSub.sub a.c0 b.c0 ha.1 hb.1,
   ←XRq_ComplexSub.sub a.c1 b.c1 ha.2 hb.2]
 simp only [mapR_bind,bind_map,map_ok]
 rfl
#print axioms sub
end XRq_QmSub
