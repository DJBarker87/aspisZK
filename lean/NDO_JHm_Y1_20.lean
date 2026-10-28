import NDO_JHm_FieldValue
import NDO_JHm_Arithmetic
import NDO_JGi_Y1Cell20
import NDO_JGi_Y1Cell21
import NDO_JGi_Y1Cell22
import NDO_JGi_Y1Cell23
import NDO_JGi_Y1Cell24
import NDO_JGi_Y1Cell25
import NDO_JGi_Y1Cell26
import NDO_JGi_Y1Cell27
import NDO_JGi_Y1Cell28
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Y1_20
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
theorem source20 : ClaimParser.field JGe_Payload27.value 20#usize=ok (JHm_FieldValue.value JGi_Y1Cell20.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell20.selected JGi_Y1Cell20.bounds
#print axioms source20
theorem numeric20 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell20.arr).c0=(JHm_Arithmetic.row 5)[20]'(by decide) := by
  rfl
#print axioms numeric20
theorem source21 : ClaimParser.field JGe_Payload27.value 21#usize=ok (JHm_FieldValue.value JGi_Y1Cell21.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell21.selected JGi_Y1Cell21.bounds
#print axioms source21
theorem numeric21 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell21.arr).c0=(JHm_Arithmetic.row 5)[21]'(by decide) := by
  rfl
#print axioms numeric21
theorem source22 : ClaimParser.field JGe_Payload27.value 22#usize=ok (JHm_FieldValue.value JGi_Y1Cell22.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell22.selected JGi_Y1Cell22.bounds
#print axioms source22
theorem numeric22 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell22.arr).c0=(JHm_Arithmetic.row 5)[22]'(by decide) := by
  rfl
#print axioms numeric22
theorem source23 : ClaimParser.field JGe_Payload27.value 23#usize=ok (JHm_FieldValue.value JGi_Y1Cell23.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell23.selected JGi_Y1Cell23.bounds
#print axioms source23
theorem numeric23 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell23.arr).c0=(JHm_Arithmetic.row 5)[23]'(by decide) := by
  rfl
#print axioms numeric23
theorem source24 : ClaimParser.field JGe_Payload27.value 24#usize=ok (JHm_FieldValue.value JGi_Y1Cell24.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell24.selected JGi_Y1Cell24.bounds
#print axioms source24
theorem numeric24 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell24.arr).c0=(JHm_Arithmetic.row 5)[24]'(by decide) := by
  rfl
#print axioms numeric24
theorem source25 : ClaimParser.field JGe_Payload27.value 25#usize=ok (JHm_FieldValue.value JGi_Y1Cell25.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell25.selected JGi_Y1Cell25.bounds
#print axioms source25
theorem numeric25 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell25.arr).c0=(JHm_Arithmetic.row 5)[25]'(by decide) := by
  rfl
#print axioms numeric25
theorem source26 : ClaimParser.field JGe_Payload27.value 26#usize=ok (JHm_FieldValue.value JGi_Y1Cell26.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell26.selected JGi_Y1Cell26.bounds
#print axioms source26
theorem numeric26 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell26.arr).c0=(JHm_Arithmetic.row 5)[26]'(by decide) := by
  rfl
#print axioms numeric26
theorem source27 : ClaimParser.field JGe_Payload27.value 27#usize=ok (JHm_FieldValue.value JGi_Y1Cell27.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell27.selected JGi_Y1Cell27.bounds
#print axioms source27
theorem numeric27 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell27.arr).c0=(JHm_Arithmetic.row 5)[27]'(by decide) := by
  rfl
#print axioms numeric27
theorem source28 : ClaimParser.field JGe_Payload27.value 28#usize=ok (JHm_FieldValue.value JGi_Y1Cell28.arr) :=
  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)
    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell28.selected JGi_Y1Cell28.bounds
#print axioms source28
theorem numeric28 : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed
    (JHm_FieldValue.value JGi_Y1Cell28.arr).c0=(JHm_Arithmetic.row 5)[28]'(by decide) := by
  rfl
#print axioms numeric28
end AspisR1.JHm_Y1_20
end
