import NDO_JFv_FieldDecode
set_option autoImplicit false
namespace AspisR1.JFv_SemanticDecode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft

def roundRow (r : Fin 10) : U8 := U8.ofNat (15+r.val) (by have h:=r.isLt;change 15+r.val ≤ 255;omega)

theorem row_value (r : Fin 10) : (roundRow r).val=15+r.val := by simp [roundRow]
theorem row_width (r : Fin 10) : (rowShape (roundRow r).val).2=896 := by
  rw [row_value]
  have bound := r.isLt
  interval_cases h : r.val <;> decide

theorem initial (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ vr running,r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok vr) ∧
      AspisS1ExtractedRoundChildren.decodeMain 1#usize vr 0#usize=ok (.Ok running) :=
  JFv_FieldDecode.success bytes pre parsed 14#u8 (by decide) (by decide) 1#usize 0#usize (by decide)

theorem round (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) (r : Fin 10) :
    ∃ vr coeffs,r1_wire.Prefix.validated_record pre (roundRow r)=ok (.Ok vr) ∧
      AspisS1ExtractedRoundChildren.decodeMain 28#usize vr 0#usize=ok (.Ok coeffs) := by
  apply JFv_FieldDecode.success bytes pre parsed (roundRow r)
  · rw [row_value];have h:=r.isLt;omega
  · rw [row_value];omega
  · rw [row_width];decide

#print axioms row_value
#print axioms row_width
#print axioms initial
#print axioms round
end AspisR1.JFv_SemanticDecode
