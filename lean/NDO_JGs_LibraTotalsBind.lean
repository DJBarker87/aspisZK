import RPv_FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraTotalsBind
open Aeneas Aeneas.Std Result ControlFlow FIo_Native
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)
def thenCall {R : Type} (terms : Weights) (K : NE → NE → NE → Result R) : Result R := do
  let we8 ← Array.index_usize terms 0#usize
  let we9 ← Array.index_usize terms 1#usize
  let first2 ← aspis_core.field.wide_exact.WideExact.add we8 we9
  let we10 ← Array.index_usize terms 2#usize
  let first3 ← aspis_core.field.wide_exact.WideExact.add first2 we10
  let we11 ← Array.index_usize terms 3#usize
  let all ← aspis_core.field.wide_exact.WideExact.add first3 we11
  K first2 first3 all
/-- A single symbolic chunk, with its remaining continuation opaque. -/
theorem source {R : Type} (terms : Weights) (K : NE → NE → NE → Result R) :
    thenCall terms K=(do let (first2,first3,all) ← FJm_LibraStages.totals terms; K first2 first3 all) := by
  unfold thenCall FJm_LibraStages.totals
  simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] <;> with_unfolding_all rfl
#print axioms source
end AspisR1.JGs_LibraTotalsBind
end
