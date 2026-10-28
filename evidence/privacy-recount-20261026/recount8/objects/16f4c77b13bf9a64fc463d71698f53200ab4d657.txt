import R1Z.ProverRwSuccessConstants
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessParser
open Aeneas Aeneas.Std Result ProverRwFull
abbrev parse := ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
abbrev parseM := ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessConstants.selected ops with op71 := parse}

theorem source (ops : ExternalFuns) (bytes : Slice U8) :
    (selected ops).op71 bytes = parse bytes := rfl

theorem base_guard (bytes : Array U8 4#usize) :
    parseM bytes =
      (if core.num.U32.from_le_bytes bytes >= ProverRwDictionaryBytesSource.aspis_core.field.P
       then .ok none else .ok (some (core.num.U32.from_le_bytes bytes))) := by
  rfl

theorem base_reject (bytes : Array U8 4#usize)
    (bad : core.num.U32.from_le_bytes bytes >= ProverRwDictionaryBytesSource.aspis_core.field.P) :
    parseM bytes = .ok none := by rw [base_guard]; simp only [bad,if_true]

theorem base_accept (bytes : Array U8 4#usize)
    (good : ¬ core.num.U32.from_le_bytes bytes >= ProverRwDictionaryBytesSource.aspis_core.field.P) :
    parseM bytes = .ok (some (core.num.U32.from_le_bytes bytes)) := by
  rw [base_guard]; simp only [good,if_false]
#print axioms source
#print axioms base_guard
#print axioms base_reject
#print axioms base_accept
end R1Z.ProverRwSuccessParser
