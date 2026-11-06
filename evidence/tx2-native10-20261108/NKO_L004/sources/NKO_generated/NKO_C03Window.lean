import PSem_Slices
import NKE_CommonCalls
set_option autoImplicit false
noncomputable section
namespace NKO_C03
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
abbrev E := aspis_core.field.wide_exact.WideExact

def select (proof : Slice U8) : Result (Slice U8) :=
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7495#usize,«end»:=7527#usize}

def G (reply : Option E) : core.result.Result E verifier.Error :=
 match reply with | none => .Err .Parse | some x => .Ok x

/-- Native C03 Option-to-Parse transcription, on the full child carrier. -/
theorem option_result (reply : Option E) :
 NHT_Constants.core.option.Option.ok_or reply verifier.Error.Parse=ok (G reply) := by
 cases reply <;> rfl

/-- Payload identity is proved from the actual checked index operation. -/
theorem selected (proof bytes : Slice U8) (run : select proof=ok bytes) :
 bytes.val=(proof.val.drop 7495).take 32 ∧ bytes.val.length=32 ∧
 ∀ i,i<32 → bytes.val[i]?=proof.val[7495+i]? := by
 have value := PSem_Slices.range_bytes proof bytes 7495#usize 7527#usize run
 have size := PSem_Slices.range_length proof bytes 7495#usize 7527#usize run
 change bytes.val=(proof.val.drop 7495).take 32 at value
 change bytes.val.length=32 at size
 refine ⟨value,size,?_⟩
 intro i inside
 rw [value]
 simp only [List.getElem?_take,inside,if_true,List.getElem?_drop]
 rfl

/-- Short proof fails at the checked slice, before any child decode/event. -/
theorem short (proof : Slice U8) (size : proof.val.length<7527) :
 ∀ bytes,select proof ≠ ok bytes := by
 intro bytes run
 have bounds := PSem_Slices.range_bounds proof bytes 7495#usize 7527#usize run
 change 7495≤7527 ∧ 7527≤proof.val.length at bounds
 omega

/-- Instantiate the CLOSED child on the SAME actual occurrence and retain
both Option arms. This does not claim that the enclosing parent is native. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (bytes : Slice U8) (reply : Result (Option E))
 (entered : Event.inactive bytes reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 reply=NJC_ClosedCalls.inactive bytes :=
 NKE_CommonCalls.source wr rr merkle finish d pub proof ck hash (.inactive bytes reply) entered
#print axioms option_result
#print axioms selected
#print axioms short
#print axioms at_actual
end NKO_C03
