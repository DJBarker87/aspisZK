import RPv_FJa_ExpandValue
import RPv_FJa_Expansion
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ExpansionMass
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
/-- Total mass one is DERIVED from the installed initial one write and the
complete native coordinate loop, not a premise about its output. -/
theorem value (N : Usize) (coordinates : Slice NQ) (out : Array NQ N)
    (hc : ∀ x∈coordinates.val,Canon x) (hsize : N.val=2^coordinates.val.length)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.expand N coordinates=ok out) :
    (∑ j : Fin N.val,FIv_NativeArray.value out j.val)=1 := by
  unfold pool_v1.pair_forest_copy_terminal.Selectors.expand at run
  obtain ⟨seed,hs,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨iterator,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  have cz : canonical (Array.repeat N field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  have cs := FJa_ArrayUpdate.canonical_write _ seed 0#usize field.QM31.ONE cz FIv_NativeValue.one.1 hs
  have same : iterator=⟨coordinates,0⟩ := (Result.ok.inj hi).symm
  rw [same] at run
  have v := FJa_ExpandValue.loop _ seed out 1#usize hc cs run
  simp only [List.drop_zero,show (1#usize).val=1 from rfl] at v
  rw [Fin.sum_univ_eq_sum_range,hsize]
  simp_rw [v]
  have hm := FJa_ExpandModel.mass (coordinates.val.map decode) 1 (FIv_NativeArray.value seed)
  simp only [List.length_map,Nat.mul_one] at hm
  rw [hm,Finset.sum_range_one,FJa_ArrayUpdate.value _ seed 0#usize field.QM31.ONE hs 0]
  simpa only [show (0#usize).val=0 from rfl,↓reduceIte] using FIv_NativeValue.one.2
#print axioms value
end AspisR1.FJa_ExpansionMass
end
