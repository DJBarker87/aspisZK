import R1Z.PV_Canon_Carrier
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem parse_m31 (bytes : Array U8 4#usize) (x : aspis_core.field.M31)
    (h : ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes bytes = .ok (some x)) : M x := by
  unfold ProverRwSuccessParserSource.aspis_core.field.M31.from_le_bytes at h
  simp only [lift,bind_tc_ok] at h
  split at h
  · cases h
  · rename_i bound
    cases h
    exact Nat.lt_of_not_ge bound
#print axioms parse_m31
end R1Z.PV_Canon
