import NKO_C03Source
set_option autoImplicit false
noncomputable section
namespace NKO_C03
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
/-- Native G for the reviewed inactive window, with the CLOSED decoder
instantiated at its exact source slice. No independently selected child reply. -/
def nativeStep (proof : Slice U8) : R E := do
 let bytes ← select proof
 let reply ← NJC_ClosedCalls.inactive bytes
 ok (G reply)

def sourceStep (proof : Slice U8) : R E := do
 let start ← NHT_Constants.compact.OFF_INACTIVE
 let stop ← NHT_Constants.compact.OFF_ROUND0
 let bytes ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start,«end»:=stop}
 let reply ← NJC_ClosedCalls.inactive bytes
 NHT_Constants.core.option.Option.ok_or reply (.Parse : verifier.Error)

/-- All returning, parse-error, abort and divergence arms are retained. -/
theorem step_source (proof : Slice U8) : nativeStep proof=sourceStep proof := by
 unfold sourceStep
 rw [NKO_Offsets.inactive,bind_tc_ok,NKO_Offsets.round0,bind_tc_ok]
 simp only [option_result]
 rfl

theorem select_abort (proof : Slice U8) (size : proof.val.length<7527) :
 select proof=fail .panic := by
 simp only [select,Slice.index_SliceIndexRangeUsizeSliceInst]
 unfold core.slice.index.SliceIndexRangeUsizeSlice.index
 split
 · rename_i h
   have bound : 7527≤proof.val.length := h.2
   omega
 · rfl

theorem source_abort (proof : Slice U8) (size : proof.val.length<7527) :
 sourceStep proof=fail .panic := by
 rw [←step_source]
 unfold nativeStep
 rw [select_abort proof size]
 rfl

/-- Complete source-side C03 installation on the actual current-proof event.
Native payload/frame/control receipts remain separately reviewable. -/
theorem occurrence (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (bytes : Slice U8) (reply : Result (Option E))
 (entered : Event.inactive bytes reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 select proof=ok bytes ∧ bytes.val=(proof.val.drop 7495).take 32 ∧
 bytes.val.length=32 ∧ reply=NJC_ClosedCalls.inactive bytes := by
 have range : select proof=ok bytes := source wr rr merkle finish d pub proof ck hash _ entered
 have payload := selected proof bytes range
 exact ⟨range,payload.1,payload.2.1,at_actual wr rr merkle finish d pub proof ck hash bytes reply entered⟩
#print axioms step_source
#print axioms select_abort
#print axioms source_abort
#print axioms occurrence
end NKO_C03
