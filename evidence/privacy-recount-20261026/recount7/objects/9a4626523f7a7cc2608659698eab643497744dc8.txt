import R1Z.PV_Join_Canonical5
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
namespace R1Z.PV_Join_ParseScalarCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5

theorem parsed (bytes : Array U8 4#usize) (x : aspis_core.field.M31)
    (success : ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes = .ok (some x)) :
    M x := by
  unfold ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes at success
  simp only [lift,bind_tc_ok] at success
  split at success
  · cases success
  · rename_i h
    cases success
    exact Nat.lt_of_not_ge h

#print axioms parsed
end R1Z.PV_Join_ParseScalarCanonical5
