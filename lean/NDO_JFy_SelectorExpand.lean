import NDO_JFy_SelectorOuter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorExpand
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_copy_terminal

theorem source (N : Usize) (coordinates : Slice NQ) (cap : 2^coordinates.length≤N.val)
    (hc : ∀ x∈coordinates.val,Canon x) :
    ∃ out,Selectors.expand N coordinates=ok out ∧ FIw_ArrayValue.canonical out := by
  have positive : 0<N.val := lt_of_lt_of_le (Nat.two_pow_pos _) cap
  have hz : FIw_ArrayValue.canonical (Array.repeat N field.QM31.ZERO) := by
    intro x hx
    have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    exact same ▸ FIv_NativeValue.zero.1
  obtain ⟨initial,update,hinit⟩ := JFy_ArrayTotal.update (Array.repeat N field.QM31.ZERO)
    0#usize field.QM31.ONE (by simpa using positive) hz FIv_NativeValue.one.1
  obtain ⟨out,run,hout⟩ := JFy_SelectorOuter.source coordinates.val
    (⟨coordinates,0⟩ : core.slice.iter.Iter NQ) initial 1#usize 0 rfl rfl
    (by simpa only [Nat.zero_add] using cap) hinit hc
  refine ⟨out,?_,hout⟩
  unfold Selectors.expand
  dsimp only
  rw [update,bind_tc_ok]
  exact run
#print axioms source
end AspisR1.JFy_SelectorExpand
end
