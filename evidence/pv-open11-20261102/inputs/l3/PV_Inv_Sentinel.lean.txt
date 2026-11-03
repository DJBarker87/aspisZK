import R1Z.PV_Inv_NativeInverseM
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_Sentinel
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47

def constructorInverse (sentinel : U32) : Result (Option U32) :=
  if sentinel=0#u32 then ok none else do
    let inv ← inverse_ref sentinel
    ok (some inv)

theorem zero_reject : constructorInverse (0#u32)=ok none := by simp [constructorInverse]

theorem nonzero_success (s : U32) (nonzero : s ≠ 0#u32) :
    ∃ inv, constructorInverse s=ok (some inv) ∧ inv.val < AspisCircleGroupOrder.P := by
  obtain ⟨inv,hr,hc,_⟩ := ProverCommitInterpolationInverse48.inverse_exact s nonzero
  exact ⟨inv,by simp [constructorInverse,nonzero,hr],hc⟩

#print axioms zero_reject
#print axioms nonzero_success
end R1Z.PV_Inv_Sentinel
