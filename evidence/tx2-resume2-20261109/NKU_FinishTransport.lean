import NKU_FinishFactor
import NKU_SemanticSource
set_option autoImplicit false
noncomputable section
namespace NKU_FinishTransport
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 finishTailG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho queries r=
 NKU_SemanticSource.run d s next «end» state a3 a4 g k a0 a1 rho queries r := by
 rw [NKU_FinishFactor.source]
 unfold NKU_FinishFactor.run NKU_SemanticSource.run NKU_ZSource.run
 simp_rw [NKU_TailSource.source]
#print axioms source
end NKU_FinishTransport
