import S1ClaimsUnrolledHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1ClaimsSourceReads
open AspisS1ClaimsUnrolledSource

/-- TOTAL concrete source record lookup, including ordinary invalid-row errors.
No parser/caller success or independently successful index is assumed. -/
theorem record_total (prefix1 : r1_wire.Prefix) (row : U8) :
    ∃ answer, r1_wire.Prefix.record prefix1 row = ok answer := by
  by_cases rejected : row >= 27#u8
  · exact ⟨.Err .InvalidRow, by simp [r1_wire.Prefix.record,rejected]⟩
  · have bound : (UScalar.cast .Usize row).val < prefix1.records.val.length := by
      scalar_tac
    obtain ⟨frame,read,_⟩ := WP.spec_imp_exists
      (Array.index_usize_spec prefix1.records (UScalar.cast .Usize row) bound)
    exact ⟨.Ok frame,by simp [r1_wire.Prefix.record,rejected,lift,bind_tc_ok,read]⟩

/-- TOTAL full native token construction on the same source result. -/
theorem validated_record_total (prefix1 : r1_wire.Prefix) (row : U8) :
    ∃ answer, r1_wire.Prefix.validated_record prefix1 row = ok answer := by
  obtain ⟨answer,read⟩ := record_total prefix1 row
  cases answer with
  | Ok frame => exact ⟨.Ok {row,framed:=frame},by simp [r1_wire.Prefix.validated_record,read,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]⟩
  | Err error => exact ⟨.Err error,by simp [r1_wire.Prefix.validated_record,read,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Aeneas.Std.core.convert.FromSame]⟩

/-- The exact source row25 used by both Claims bodies is derived from the
complete Prefix, rather than supplied as a successful child premise. -/
theorem record25_exact (prefix1 : r1_wire.Prefix) :
    ∃ frame, Array.index_usize prefix1.records 25#usize = ok frame ∧
      r1_wire.Prefix.record prefix1 25#u8 = ok (.Ok frame) ∧
      r1_wire.Prefix.validated_record prefix1 25#u8 =
        ok (.Ok {row:=25#u8,framed:=frame}) := by
  obtain ⟨frame,read,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec prefix1.records 25#usize (by scalar_tac))
  have cast : UScalar.cast .Usize 25#u8 = 25#usize := by scalar_tac
  have lookup : r1_wire.Prefix.record prefix1 25#u8 = ok (.Ok frame) := by
    simp [r1_wire.Prefix.record,cast,lift,bind_tc_ok,read]
  exact ⟨frame,read,lookup,by simp [r1_wire.Prefix.validated_record,lookup,
    Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]⟩

#print axioms record_total
#print axioms validated_record_total
#print axioms record25_exact
end AspisS1ClaimsSourceReads
