import NFE_NFC_FirstSource
import NFC_CheckedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_FirstGeometry
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources

theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (inside : slot.val<4) (value : NE) (scalar : NQ)
    (run : first q g slot=ok (value,scalar)) :
    ∃ start stop, NFA_TailQM.read q start stop=ok scalar ∧
      start.val=slot.val*120+104 ∧ stop.val=slot.val*120+120 ∧
      stop.val=start.val+16 ∧ stop.val≤480 := by
  obtain ⟨base,start,stop,_,mul,startEq,stopEq,decode⟩:=NFE_NFC_FirstSource.cut q g slot value scalar run
  have b:=NFC_CheckedArithmetic.mul slot 120#usize base (by scalar_tac) mul
  have a:=NFC_CheckedArithmetic.add base 104#usize start (by scalar_tac) startEq
  have z:=NFC_CheckedArithmetic.add base 120#usize stop (by scalar_tac) stopEq
  refine ⟨start,stop,decode,?_,?_,?_,?_⟩ <;> scalar_tac
#print axioms accepted
end AspisR1.NFE_NFC_FirstGeometry
end
