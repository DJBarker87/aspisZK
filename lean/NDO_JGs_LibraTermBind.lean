import RPv_FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraTermBind
open Aeneas Aeneas.Std Result ControlFlow FIo_Native
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)
def thenCall {R : Type} (ap1 : Weights) (high : Array NQ 4#usize) (j : Usize) (K : Usize → NE → Result R) : Result R := do
  let i ← Array.index_usize FIo_Native.weights.PERM j
  let we ← Array.index_usize ap1 i
  let q ← Array.index_usize high j
  let we1 ← aspis_core.field.wide_exact.WideExact.mul_qm31 we q
  let term ← aspis_core.field.wide_exact.WideExact.mul_m31 we1 FIo_Native.weights.QUARTER
  K i term
/-- A single symbolic chunk, with its remaining continuation opaque. -/
theorem source {R : Type} (ap1 : Weights) (high : Array NQ 4#usize) (j : Usize) (K : Usize → NE → Result R) :
    thenCall ap1 high j K=(do let (i,t) ← FJm_LibraStages.term ap1 high j; K i t) := by
  unfold thenCall FJm_LibraStages.term
  simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] <;> with_unfolding_all rfl
#print axioms source
end AspisR1.JGs_LibraTermBind
end
