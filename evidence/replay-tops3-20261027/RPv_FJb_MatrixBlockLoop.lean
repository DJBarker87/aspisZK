import RPv_FJb_MatrixBlock
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixBlock
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
theorem unfold_loop (s : State) (g : Usize) (hg : g.val < 4) :
    state_only_poseidon.external_linear_lazy_loop0 s g=(do
      let out ← block s g
      let next ← g+1#usize
      state_only_poseidon.external_linear_lazy_loop0 out next) := by
  rw [state_only_poseidon.external_linear_lazy_loop0.eq_def]
  have hlt : g < 4#usize := by scalar_tac
  rw [if_pos hlt]
  simp only [block,bind_assoc_eq]

#print axioms unfold_loop
end AspisR1.FJb_MatrixBlock
end
