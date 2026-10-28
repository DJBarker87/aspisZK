import NDO_JGj_ThreeLoopTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ThreeTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
open FJe_ThreeColumnStep (Weights)
theorem source (w : Weights) (c0 c1 c2 : Constants)
    (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
    ∃ out,state_only_poseidon.interpolate_three_constant_columns w c0 c1 c2=ok out ∧ canonical out := by
  have zero : canonical (Array.repeat 16#usize field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  exact JGj_ThreeLoopTotal.source 16 0#usize _ w c0 c1 c2 rfl zero hw h0 h1 h2
#print axioms source
end AspisR1.JGj_ThreeTotal
end
