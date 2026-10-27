import R1Z.PV_CBL_BlockValueBoundary
import R1Z.PV_CBL_BlockStage09
import R1Z.PV_CBL_BlockFourValue
import R1Z.PV_CBL_BlockScheduleValue
import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockStage08
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
def source (original : Array U32 8#usize) (abef cdgh : A4)
    (w0 w1 w2 w3 : A4) : Result (Array U32 8#usize) := do
  let w ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w0 w1 w2 w3
  let (a,c) ← PV_CBL_FallbackFourModel.source abef cdgh w PV_CBL_FallbackConstantMatrix.q8
  PV_CBL_BlockStage09.source original a c w1 w2 w3 w
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
  let w := PV_CBL_BlockValueBoundary.schedule w0 w1 w2 w3
  let current := PV_CBL_BlockValueBoundary.four current w PV_CBL_FallbackConstantMatrix.q8
  PV_CBL_BlockStage09.value original current w1 w2 w3 w
theorem shape (original current : State) (w0 w1 w2 w3 : A4) :
    source (PV_CBL_FallbackStateCodec.encode original)
      (pack current.a current.b current.e current.f) (pack current.c current.d current.g current.h)
      w0 w1 w2 w3 = ok (PV_CBL_FallbackStateCodec.encode (value original current w0 w1 w2 w3)) := by
  unfold source value
  rw [PV_CBL_BlockValueBoundary.schedule_source]
  simp only [bind_tc_ok]
  generalize hw : PV_CBL_BlockValueBoundary.schedule w0 w1 w2 w3 = word
  rw [PV_CBL_BlockValueBoundary.four_source]
  rw [PV_CBL_BlockValueBoundary.packed_bind]
  exact PV_CBL_BlockStage09.shape original (PV_CBL_BlockValueBoundary.four current word PV_CBL_FallbackConstantMatrix.q8) w1 w2 w3 word
#print axioms source
#print axioms value
#print axioms shape
end R1Z.PV_CBL_BlockStage08
