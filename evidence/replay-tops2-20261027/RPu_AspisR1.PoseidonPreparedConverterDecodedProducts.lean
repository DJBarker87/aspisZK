import RPu_AspisR1.PoseidonPreparedSum3ProductAlgebra
import RPu_AspisR1.PoseidonPreparedRowModelSumProducts
import RPu_AspisR1.PoseidonPreparedKaratsubaValue

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedConverterDecodedProducts
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev U64 := UScalar UScalarTy.U64

private def rowModel := AspisR1.PoseidonPreparedChannelRowValue.rowModel
private def decodeQM := AspisR1.PoseidonPreparedKaratsubaValue.decodeQM

theorem converter_decoded_products (out : AspisR1SelectedMaskProbe.field.QM31)
    (r00 r01 r02 r10 r11 r12 r20 r21 r22 : U64)
    (x0 x1 x2 y0 y1 y2 : QMExact)
    (hdecoded : decodeQM out =
      ⟨rowModel r00 r01 r02 + (⟨2,1⟩ : CMExact) * rowModel r10 r11 r12,
        rowModel r20 r21 r22 - rowModel r00 r01 r02 - rowModel r10 r11 r12⟩)
    (h0 : rowModel r00 r01 r02 = x0.re*y0.re + x1.re*y1.re + x2.re*y2.re)
    (h1 : rowModel r10 r11 r12 = x0.im*y0.im + x1.im*y1.im + x2.im*y2.im)
    (h2 : rowModel r20 r21 r22 = (x0.re+x0.im)*(y0.re+y0.im) +
      (x1.re+x1.im)*(y1.re+y1.im) + (x2.re+x2.im)*(y2.re+y2.im)) :
    decodeQM out = x0*y0 + x1*y1 + x2*y2 := by
  rw [hdecoded, h0, h1, h2]
  have hR : (⟨2,1⟩ : CMExact) = AspisV8R15.ExactTowerBase.qm31R := by rfl
  rw [hR]
  exact AspisR1.PoseidonPreparedSum3ProductAlgebra.sum3_qm_products
    x0.re x0.im x1.re x1.im x2.re x2.im
    y0.re y0.im y1.re y1.im y2.re y2.im

#print axioms converter_decoded_products
end AspisR1.PoseidonPreparedConverterDecodedProducts
