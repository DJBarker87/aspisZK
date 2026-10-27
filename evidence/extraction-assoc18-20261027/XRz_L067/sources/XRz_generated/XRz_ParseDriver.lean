import XRz_ParseFold
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_ParseDriver
/-- Complete27-record parser, including rejected/failing prefixes, factored
through the generic first-stop fold. No field-validation law is assumed. -/
theorem source (bytes : Slice U8) : r1_wire.Prefix.parse bytes=XRz_ParseFold.parse bytes := by
 by_cases short : Slice.len bytes < 32#usize
 · conv_lhs => unfold r1_wire.Prefix.parse; rw [if_pos short]
   conv_rhs => unfold XRz_ParseFold.parse; rw [if_pos short]
 · conv_lhs => unfold r1_wire.Prefix.parse; rw [if_neg short]
   conv_rhs => unfold XRz_ParseFold.parse; rw [if_neg short]
   congr 1
   funext first
   congr 1
   funext root
   cases root with
   | Err e => rfl
   | Ok root =>
    rw [←XRx_TryDriver.source]
    repeat' (first
     | rfl
     | (conv_rhs => rw [XRx_TryDriver.run]; unfold XRz_ParseFold.step
                    simp only [bind_assoc_eq,bind_tc_ok])
     | (conv_rhs => simp only [XRz_ParseFold.row,Nat.reduceAdd,Nat.reduceLT,
                    _root_.dite_true,U8.ofNat])
     | (congr 1; funext out; cases out))

#print axioms source
end XRz_ParseDriver
