import NHT_FinishRun
set_option autoImplicit false
noncomputable section
namespace NHT_FinishNewPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHT_FinishChain
variable {W : Type}
def installed (ops : Ops W) (packet : Result (R W)) : Ops W :=
 {ops with op3:=fun _ _ _=>packet}
/-- Replace only the NEW child on this actual Prepared record. Its entire
error/failure/divergence carrier is retained. -/
theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (alpha0 alpha1 : E)
 (packet : Result (R W))
 (NHM_new : ops.op3 p.variant p.semantic_alpha p.z=packet) :
 NHT_FinishRun.run ops v p a obs ws pair alpha0 alpha1 =
 NHT_FinishRun.run (installed ops packet) v p a obs ws pair alpha0 alpha1 := by
 unfold NHT_FinishRun.run NHT_FinishRun.afterFirst NHT_FinishChain.afterRound
 simp only [installed]
 rw [NHM_new]
 rfl
#print axioms source
end NHT_FinishNewPacket
