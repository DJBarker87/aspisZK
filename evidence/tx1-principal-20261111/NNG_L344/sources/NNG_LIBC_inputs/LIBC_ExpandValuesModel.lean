import NGV_ExpandPacket
set_option autoImplicit false
namespace LIBC_ExpandValuesModel
open Aeneas Aeneas.Std Result
/-- Pointwise CLOSED leaf model, independent of the native invocation relation. -/
def output (src before : Slice U8) : Slice U8 :=
 ⟨List.ofFn (fun j : Fin before.val.length => NFU_Retarget.LPl_A.Expand.byte src.val j.val), by
  simpa only [List.length_ofFn] using before.property⟩
theorem source (src before : Slice U8) (bound : src.val.length ≤ 1856) :
 NFU_Retarget.compact.expand_values src before =
 ok (if src.val.length % 16 = 0 ∧ before.val.length = 2 * src.val.length
  then (.Ok (),output src before) else (.Err .Length,before)) := by
 by_cases good : src.val.length % 16 = 0 ∧ before.val.length = 2 * src.val.length
 · rw [if_pos good]
   obtain ⟨after,run,size,points⟩ := NGV_ExpandPacket.result src before bound good.1 good.2
   have same : after = output src before := by
    apply Subtype.ext
    apply List.ext_getElem
    · simpa only [output,List.length_ofFn] using size
    · intro j hj hk
      have point := points j (by omega)
      rw [List.getElem?_eq_getElem hj] at point
      simpa only [Option.getD_some,output,List.getElem_ofFn] using point
   simpa only [same] using run
 · rw [if_neg good]
   exact NFU_CompactLeaves.expand_reject src before bound (by omega)
#print axioms source
end LIBC_ExpandValuesModel
