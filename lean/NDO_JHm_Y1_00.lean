import NDO_JHm_FieldValue
import NDO_JHm_Arithmetic
import NDO_JGi_Y1Cell00
import NDO_JGi_Y1Cell01
import NDO_JGi_Y1Cell02
import NDO_JGi_Y1Cell03
import NDO_JGi_Y1Cell04
import NDO_JGi_Y1Cell05
import NDO_JGi_Y1Cell06
import NDO_JGi_Y1Cell07
import NDO_JGi_Y1Cell08
import NDO_JGi_Y1Cell09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Y1_00
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
theorem source00 : ClaimParser.field JGe_Payload27.value 0#usize=ok (JHm_FieldValue.value JGi_Y1Cell00.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell00.selected JGi_Y1Cell00.bounds
#print axioms source00
theorem numeric00 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell00.arr).c0=(JHm_Arithmetic.row 5)[0]'(by decide) := by
  rfl
#print axioms numeric00
theorem source01 : ClaimParser.field JGe_Payload27.value 1#usize=ok (JHm_FieldValue.value JGi_Y1Cell01.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell01.selected JGi_Y1Cell01.bounds
#print axioms source01
theorem numeric01 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell01.arr).c0=(JHm_Arithmetic.row 5)[1]'(by decide) := by
  rfl
#print axioms numeric01
theorem source02 : ClaimParser.field JGe_Payload27.value 2#usize=ok (JHm_FieldValue.value JGi_Y1Cell02.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell02.selected JGi_Y1Cell02.bounds
#print axioms source02
theorem numeric02 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell02.arr).c0=(JHm_Arithmetic.row 5)[2]'(by decide) := by
  rfl
#print axioms numeric02
theorem source03 : ClaimParser.field JGe_Payload27.value 3#usize=ok (JHm_FieldValue.value JGi_Y1Cell03.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell03.selected JGi_Y1Cell03.bounds
#print axioms source03
theorem numeric03 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell03.arr).c0=(JHm_Arithmetic.row 5)[3]'(by decide) := by
  rfl
#print axioms numeric03
theorem source04 : ClaimParser.field JGe_Payload27.value 4#usize=ok (JHm_FieldValue.value JGi_Y1Cell04.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell04.selected JGi_Y1Cell04.bounds
#print axioms source04
theorem numeric04 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell04.arr).c0=(JHm_Arithmetic.row 5)[4]'(by decide) := by
  rfl
#print axioms numeric04
theorem source05 : ClaimParser.field JGe_Payload27.value 5#usize=ok (JHm_FieldValue.value JGi_Y1Cell05.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell05.selected JGi_Y1Cell05.bounds
#print axioms source05
theorem numeric05 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell05.arr).c0=(JHm_Arithmetic.row 5)[5]'(by decide) := by
  rfl
#print axioms numeric05
theorem source06 : ClaimParser.field JGe_Payload27.value 6#usize=ok (JHm_FieldValue.value JGi_Y1Cell06.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell06.selected JGi_Y1Cell06.bounds
#print axioms source06
theorem numeric06 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell06.arr).c0=(JHm_Arithmetic.row 5)[6]'(by decide) := by
  rfl
#print axioms numeric06
theorem source07 : ClaimParser.field JGe_Payload27.value 7#usize=ok (JHm_FieldValue.value JGi_Y1Cell07.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell07.selected JGi_Y1Cell07.bounds
#print axioms source07
theorem numeric07 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell07.arr).c0=(JHm_Arithmetic.row 5)[7]'(by decide) := by
  rfl
#print axioms numeric07
theorem source08 : ClaimParser.field JGe_Payload27.value 8#usize=ok (JHm_FieldValue.value JGi_Y1Cell08.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell08.selected JGi_Y1Cell08.bounds
#print axioms source08
theorem numeric08 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell08.arr).c0=(JHm_Arithmetic.row 5)[8]'(by decide) := by
  rfl
#print axioms numeric08
theorem source09 : ClaimParser.field JGe_Payload27.value 9#usize=ok (JHm_FieldValue.value JGi_Y1Cell09.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell09.selected JGi_Y1Cell09.bounds
#print axioms source09
theorem numeric09 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell09.arr).c0=(JHm_Arithmetic.row 5)[9]'(by decide) := by
  rfl
#print axioms numeric09
end AspisR1.JHm_Y1_00
end
