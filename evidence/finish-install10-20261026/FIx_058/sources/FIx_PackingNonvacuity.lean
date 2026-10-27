import FIx_HighSum
import FIw_PackNonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PackingNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)

theorem high_source : ∃ (s : FIx_HighSumInner.Selectors) (out : NQ),
    (∀ x∈s.high.val,Canon x) ∧
    pool_v1.pair_forest_semantic_terminal.sum_high s (Array.to_slice (Array.make 0#usize []))=ok out ∧
    Canon out ∧ decode out=0 := by
  let s : FIx_HighSumInner.Selectors :=
    {high:=Array.repeat 64#usize field.QM31.ZERO,low:=Array.repeat 16#usize field.QM31.ZERO}
  have hh : ∀ x∈s.high.val,Canon x := by
    intro x hx
    have eq : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [eq]
    exact FIv_NativeValue.zero.1
  obtain ⟨out,hr,hc,hv⟩ := FIx_HighSum.source s (Array.to_slice (Array.make 0#usize []))
    (by intro r h;cases h) hh
  exact ⟨s,out,hh,hr,hc,hv⟩
#print axioms high_source
#print axioms AspisR1.FIw_PackNonvacuity.value
end AspisR1.FIx_PackingNonvacuity
end
