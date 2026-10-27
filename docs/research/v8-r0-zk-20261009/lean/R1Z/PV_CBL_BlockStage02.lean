import R1Z.PV_CBL_BlockValueBoundary
import R1Z.PV_CBL_BlockStage03
import R1Z.PV_CBL_BlockFourValue
import R1Z.PV_CBL_BlockScheduleValue
import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockStage02
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
def source (original : Array U32 8#usize) (abef cdgh : A4)
    (w0 w1 w2 w3 : A4) : Result (Array U32 8#usize) := do
  let (a,c) ← PV_CBL_FallbackFourModel.source abef cdgh w2 PV_CBL_FallbackConstantMatrix.q2
  PV_CBL_BlockStage03.source original a c w0 w1 w2 w3
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
  let current := PV_CBL_BlockValueBoundary.four current w2 PV_CBL_FallbackConstantMatrix.q2
  PV_CBL_BlockStage03.value original current w0 w1 w2 w3
theorem shape (original current : State) (w0 w1 w2 w3 : A4) :
    source (PV_CBL_FallbackStateCodec.encode original)
      (pack current.a current.b current.e current.f) (pack current.c current.d current.g current.h)
      w0 w1 w2 w3 = ok (PV_CBL_FallbackStateCodec.encode (value original current w0 w1 w2 w3)) := by
  unfold source value
  rw [PV_CBL_BlockValueBoundary.four_source]
  rw [PV_CBL_BlockValueBoundary.packed_bind]
  exact PV_CBL_BlockStage03.shape original (PV_CBL_BlockValueBoundary.four current w2 PV_CBL_FallbackConstantMatrix.q2) w0 w1 w2 w3
#print axioms source
#print axioms value
#print axioms shape
end R1Z.PV_CBL_BlockStage02
