import FJm_WrappingSuccess
import ExtractedMaskCM31Square
import FIo_FieldBridge
set_option autoImplicit false
namespace AspisR1.FJm_SquareOperand
open Aeneas Aeneas.Std Result
abbrev widen := core.convert.num.FromU64U32.from

def operand (a b : U32) : U64 :=
  U64.wrapping_mul (U64.wrapping_add (widen a) (widen b))
    (U64.wrapping_sub (U64.wrapping_add (widen a) (widen FIo_Native.aspis_core.field.P)) (widen b))

theorem value (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    ∃ product : U64,ExtractedMaskCM31Square.squareOperand a b=ok product ∧ operand a b=product ∧
      product.val=(a.val+b.val)*(a.val+2147483647-b.val) := by
  obtain ⟨product,run,numeric⟩ := ExtractedMaskCM31Square.squareOperand_success a b ha hb
  have original := run
  unfold ExtractedMaskCM31Square.squareOperand at run
  obtain ⟨left,hl,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨base,hbase,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨right,hr,hp⟩ := Port3_PushFrame.bind_success _ _ _ run
  have eleft := FJm_WrappingSuccess.add _ _ left hl
  have ebase := FJm_WrappingSuccess.add _ _ base hbase
  have eright := FJm_WrappingSuccess.sub _ _ right hr
  have eproduct := FJm_WrappingSuccess.mul _ _ product hp
  have prime : FIo_Native.aspis_core.field.P=AspisR1SelectedMaskProbe.field.P := rfl
  refine ⟨product,original,?_,numeric⟩
  unfold operand
  rw [prime,eleft,ebase,eright,eproduct]
#print axioms value
end AspisR1.FJm_SquareOperand
