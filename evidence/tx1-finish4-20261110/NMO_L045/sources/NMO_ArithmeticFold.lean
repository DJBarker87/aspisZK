import NMO_ArithmeticAtState
import NLI_SourceEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArithmeticFold
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- The actual source-ordered arithmetic suffix reaches the same guard with
its internally produced value. The rest of the code, including every later
query/error/abort prefix, is left verbatim. This is source-only, not a scalar
native cut or a row root. -/
theorem source {H : Type} (i : Input H) (running : Q) (alpha : Alpha)
 (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal mask : Q) (extra : Words)
 (he : JFv_RoundArithmetic.Canonical i.challenges.eta)
 (ht : JFv_RoundArithmetic.Canonical terminal) (hm : JFv_RoundArithmetic.Canonical mask)
 (hx : NMO_ExtraValue.Canonical extra) :
 ∃ value,JFv_RoundArithmetic.Canonical value ∧
 run (NLI_Source.suffix_multiply i running alpha transcript claims terminal mask extra)=
 run (NLI_Source.suffix_terminalGuard i running alpha transcript claims extra value) := by
 let extraCell:=NKQ_ArrayWindows.cell extra 28 (by decide)
 have hc : JFv_RoundArithmetic.Canonical extraCell:=hx _ (List.getElem_mem _)
 obtain ⟨product,mul,hp,_⟩:=NLU_FieldValues.mul_value i.reservation i.challenges.eta terminal he ht
 obtain ⟨partialValue,add1,hpartial,_⟩:=NLU_FieldValues.add_value i.reservation mask product hm hp
 obtain ⟨value,add2,hv,_⟩:=NLU_FieldValues.add_value i.reservation partialValue extraCell hpartial hc
 have getExtra:=NKQ_ArrayWindows.read extra 28#usize (by decide)
 refine ⟨value,hv,?_⟩
 unfold NLI_Source.suffix_multiply
 rw [mul]
 change run (NLI_Source.suffix_addMask i running alpha transcript claims mask extra product)=_
 unfold NLI_Source.suffix_addMask
 rw [add1]
 change run (NLI_Source.suffix_extra28 i running alpha transcript claims extra partialValue)=_
 unfold NLI_Source.suffix_extra28
 rw [getExtra]
 change run (NLI_Source.suffix_addExtra i running alpha transcript claims extra partialValue extraCell)=_
 unfold NLI_Source.suffix_addExtra
 rw [add2]
 rfl
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMO_ArithmeticFold
end
