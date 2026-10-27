import FJm_CMSquareTrace
import FJm_RealSquare
import FJm_CMSquarePack
import FIo_CMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_CMSquare
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC cm)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (x out : NC) (hx : FIo_CMValues.Canon x)
    (run : FIo_Native.aspis_core.field.CM31.square x=ok out) :
    FIo_CMValues.Canon out ∧ decodeC (cm out)=decodeC (cm x)*decodeC (cm x) := by
  obtain ⟨real,ab,imag,hr,hab,hi,rfl⟩ := FJm_CMSquareTrace.reached x out run
  have vr := FJm_RealSquare.value x.a x.b real hx.1 hx.2 hr
  have vab := FIo_M31Values.mul x.a x.b ab hab
  change FIo_Native.aspis_core.field.M31.add ab ab=ok imag at hi
  have vi := FIo_M31Values.add ab ab imag vab.1 vab.1 hi
  refine ⟨⟨vr.1,vi.1⟩,?_⟩
  change (⟨decodeM real,decodeM imag⟩ : AspisV8R15.ExactTowerBase.CM31Exact)=
    (⟨decodeM x.a,decodeM x.b⟩ : AspisV8R15.ExactTowerBase.CM31Exact)*
      (⟨decodeM x.a,decodeM x.b⟩ : AspisV8R15.ExactTowerBase.CM31Exact)
  rw [vr.2,vi.2,vab.2]
  exact FJm_CMSquarePack.tower (-1) (decodeM x.a) (decodeM x.b)
#print axioms value
end AspisR1.FJm_CMSquare
end
