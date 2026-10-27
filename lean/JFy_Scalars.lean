import JFy_Specs
import FIq_Native08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Scalars
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (v : CompiledVariant) (present : Bool) (a b c d : field.QM31)
    (ha : Canon a) (hb : Canon b) (hc : Canon c) (hd : Canon d) :
    ∃ out,scalar_lanes v present a b c d=ok out ∧ canonical out := by
  have pair (x y : field.QM31) (hx : Canon x) (hy : Canon y) : canonical (Array.make 2#usize [x,y]) := by
    intro q hq
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact hx
    · exact hy
  cases v with
  | PrivateTransfer =>
    obtain ⟨out,call,hout,_⟩ := FIv_PreparedTotal.add b c hb hc
    exact ⟨Array.make 2#usize [a,out],by unfold scalar_lanes;rw [call,bind_tc_ok],pair a out ha hout⟩
  | Withdrawal =>
    cases present with
    | false => exact ⟨Array.make 2#usize [a,b],rfl,pair a b ha hb⟩
    | true =>
      obtain ⟨out,call,hout,_⟩ := FIv_PreparedTotal.add b d hb hd
      exact ⟨Array.make 2#usize [a,out],by unfold scalar_lanes;rw [call,bind_tc_ok];rfl,pair a out ha hout⟩
#print axioms source
end AspisR1.JFy_Scalars
end
