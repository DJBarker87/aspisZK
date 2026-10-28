import RPv_FJm_LibraStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraPowersBind
open Aeneas Aeneas.Std Result ControlFlow FIo_Native
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)
def thenCall {R : Type} (extra : Array NQ 2#usize) (side : Usize) (K : Array NQ 4#usize → Array NQ 4#usize → NQ → NQ → Result R) : Result R := do
  let q ← Array.index_usize extra side
  let q1 ← aspis_core.field.QM31.mul aspis_core.field.QM31.ONE q
  let q2 ← aspis_core.field.QM31.mul q1 q
  let q3 ← aspis_core.field.QM31.mul q2 q
  let _ ← aspis_core.field.QM31.mul q3 q
  let q4 ←
    Array.index_usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, q1, q2, q3 ]) 2#usize
  let q41 ← aspis_core.field.QM31.square q4
  let q8 ← aspis_core.field.QM31.square q41
  let q12 ← aspis_core.field.QM31.mul q8 q41
  let q16 ← aspis_core.field.QM31.square q8
  K (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3])
    (Array.make 4#usize [aspis_core.field.QM31.ONE,q41,q8,q12]) q41 q16
/-- A single symbolic chunk, with its remaining continuation opaque. -/
theorem source {R : Type} (extra : Array NQ 2#usize) (side : Usize) (K : Array NQ 4#usize → Array NQ 4#usize → NQ → NQ → Result R) :
    thenCall extra side K=(do let (base,high,q4,q16) ← FJm_LibraStages.powers extra side; K base high q4 q16) := by
  unfold thenCall FJm_LibraStages.powers
  simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] <;> with_unfolding_all rfl
#print axioms source
end AspisR1.JGs_LibraPowersBind
end
