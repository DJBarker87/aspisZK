import FJe_ThreeColumnLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ThreeColumns
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights model)
open FJb_M31Step (Constants Bounded)
/-- Complete actual interpolation VALUE and canonicality on the same supplied
weights and columns. No output value/canonicality is a hypothesis. -/
theorem value (w : Weights) (c0 c1 c2 : Constants) (out : State)
    (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2)
    (run : state_only_poseidon.interpolate_three_constant_columns w c0 c1 c2=ok out) :
    canonical out ∧ decoded out=model w c0 c1 c2 := by
  have zero : canonical (Array.repeat 16#usize field.QM31.ZERO) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact FIv_NativeValue.zero.1
  have v := FJe_ThreeColumnLoop.value 16 0#usize
    (Array.repeat 16#usize field.QM31.ZERO) out w c0 c1 c2 rfl hw h0 h1 h2 zero run
  refine ⟨v.1,?_⟩
  funext j
  have hv := v.2 j
  have cond : (0#usize).val≤j.val := by change 0≤j.val;exact Nat.zero_le _
  rw [if_pos cond] at hv
  exact hv
#print axioms value
end AspisR1.FJe_ThreeColumns
end
