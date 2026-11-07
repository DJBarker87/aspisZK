import NFU_CompactLeaves
import NGV_ByteWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Expansion179
open Aeneas Aeneas.Std Result
open NFU_Retarget
/-- The compact y1 slice at the actual frozen prepare call site. -/
def compactInput (proof : Slice U8) : Slice U8 := NGV_ByteWindow.select proof 7031 464
theorem compact_length (proof : Slice U8) (size : proof.val.length=57607) :
 (compactInput proof).val.length=464 :=
 NGV_ByteWindow.select_length proof 7031 464 (by omega)
/-- Recover the exact NativeTrace at a returning expansion occurrence, using
its CLOSED total law and deterministic Result. No unrelated expansion witness
or successful constructor is selected. This is an internal caller lemma. -/
theorem same_call (compact before y1 : Slice U8)
 (compact_length : compact.val.length=464) (before_length : before.val.length=928)
 (call : NFU_Retarget.compact.expand_values compact before=ok (.Ok (),y1)) :
 LPn.Expand.NativeTrace compact.val before.val 29 y1.val := by
 obtain ⟨out,trace⟩ := LPn.Expand.total compact.val before.val 29
 have inherited := LPn.Expand.to_inherited compact.val before.val out 29 trace
 have size := LPl.Expand.length compact.val before.val out 29 inherited
 let output : Slice U8 := ⟨out,by rw [size];exact before.property⟩
 have trace' : LPn.Expand.NativeTrace compact.val before.val (compact.val.length/16) output.val := by
  simpa only [compact_length] using trace
 have returned := NFU_CompactLeaves.expand_result compact before output
  (by omega) (by rw [compact_length]) (by rw [compact_length,before_length]) trace'
 have pair := Result.ok.inj (returned.symm.trans call)
 have same : output=y1 := congrArg Prod.snd pair
 simpa only [←same] using trace
#print axioms compact_length
#print axioms same_call
#print same_call
end AspisR1.NMP_Expansion179
end
