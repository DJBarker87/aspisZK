import FJa_SquareValue
import FIo_QMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_SquareBridge
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ qm)

def toMask (x : NQ) : FIv_NativeArithmetic.NQ :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

/-- Coordinate-only source association of the same optimized square body. -/
theorem mapped (x : NQ) :
    FIv_Map.map toMask (FIo_Native.aspis_core.field.QM31.square x)=
      FIq_Native.field.QM31.square (toMask x) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

theorem value (x out : NQ) (hx : FIo_QMValues.Canon x)
    (run : FIo_Native.aspis_core.field.QM31.square x=ok out) :
    FIo_QMValues.Canon out ∧ AspisR1CurrentWide.Proof.decodeQM (qm out)=
      AspisR1CurrentWide.Proof.decodeQM (qm x)*AspisR1CurrentWide.Proof.decodeQM (qm x) := by
  have h := mapped x
  rw [run,FIv_Map.map_ok] at h
  exact FJa_SquareValue.value (toMask x) (toMask out) hx h.symm
#print axioms mapped
#print axioms value
end AspisR1.FJm_SquareBridge
end
