import XSe_ValidatorTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_RecordDomain
/-- Source row geometry bounds every reached validator payload by116 fields. -/
theorem source (row tag : U8) (size : Usize)
 (run : r1_wire.row_shape row=ok (some (tag,size))) : size.val≤3712 := by
 unfold r1_wire.row_shape at run
 simp only [r1_wire.CLAIMS,r1_wire.LANES,r1_wire.POINTS] at run
 repeat' first
 | split at run
 | simp only [bind_tc_ok] at run
 | (cases run <;> scalar_tac)
#print axioms source
end XSe_RecordDomain
