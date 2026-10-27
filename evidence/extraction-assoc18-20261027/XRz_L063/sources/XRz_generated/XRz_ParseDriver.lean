import XRz_ParseFold
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_ParseDriver
/-- Complete27-record parser, including rejected/failing prefixes, factored
through the generic first-stop fold. No field-validation law is assumed. -/
theorem source (bytes : Slice U8) : r1_wire.Prefix.parse bytes=XRz_ParseFold.parse bytes := by
 unfold r1_wire.Prefix.parse XRz_ParseFold.parse
 split
 · rfl
 · congr 1
   funext first
   congr 1
   funext root
   cases root with
   | Err e => rfl
   | Ok root =>
    rw [←XRx_TryDriver.source]
    simp only [XRx_TryDriver.run,XRz_ParseFold.step,XRz_ParseFold.row,Nat.reduceAdd,Nat.reduceLT,
     _root_.dite_true,U8.ofNat,core.result.Result.Insts.CoreOpsTry.branch,bind_assoc_eq]
    repeat' (first
     | rfl
     | (dsimp! only)
     | (simp only [bind_tc_ok,List.nil_append,List.cons_append,List.nil_append])
     | (congr 1; funext out; cases out))
#print axioms source
end XRz_ParseDriver
