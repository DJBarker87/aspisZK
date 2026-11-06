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
 have bounds : 7527≤proof.val.length := by
  simp only [select,Slice.index_SliceIndexRangeUsizeSliceInst] at run
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at run
  split at run
  · rename_i h
    exact h.2
  · cases run
 have value : bytes.val=(proof.val.drop 7495).take 32 := by
  simp only [select,Slice.index_SliceIndexRangeUsizeSliceInst] at run
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at run
  split at run
  · have same := Result.ok.inj run
    have cells := congrArg (fun s : Slice U8 => s.val) same
    simpa only [List.slice] using cells.symm
  · cases run
 have size : bytes.val.length=32 := by
  rw [value,List.length_take,List.length_drop]
  omega
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
 simp only [select,Slice.index_SliceIndexRangeUsizeSliceInst] at run
 unfold core.slice.index.SliceIndexRangeUsizeSlice.index at run
 split at run
 · rename_i h
   have bound : 7527≤proof.val.length := h.2
   omega
 · cases run

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
