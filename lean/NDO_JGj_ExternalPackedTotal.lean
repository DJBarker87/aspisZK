import NDO_JGj_PackedLoopTotal
import NDO_JGj_PackedSumTotal
import RPv_FJe_ExternalPackedValue
import NDO_JGa_Map
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalPackedTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical decoded)
theorem source (s : Array NQ 16#usize) (hs : canonical s) :
    ∃ out,state_only_poseidon.external_linear_packed s=ok out ∧ canonical out := by
  have zero : canonical (Array.repeat 4#usize field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  obtain ⟨p,rp,cp⟩ := JGj_PackedLoopTotal.source 4 0#usize s _ rfl hs zero
  obtain ⟨total,rt,ct⟩ := JGj_PackedSumTotal.source p cp
  obtain ⟨out,ro,co⟩ := JGa_Map.source FJe_ExternalCalls.callback Canon p total (by
    intro x hx
    obtain ⟨q,rq,cq,_⟩ := FIv_PreparedTotal.add x total (cp x hx) ct
    exact ⟨q,by change (do let y ← field.QM31.add x total;ok (y,total))=_;rw [rq,bind_tc_ok],cq⟩)
  refine ⟨out,?_,co⟩
  have roNative : FIq_Native.core.array.Array.map FJe_ExternalCalls.callback p total=ok out := ro
  rw [FJe_ExternalCalls.factor,rp,bind_tc_ok,rt,bind_tc_ok,roNative]
#print axioms source
end AspisR1.JGj_ExternalPackedTotal
end
