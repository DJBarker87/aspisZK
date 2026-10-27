import XSf_PrepareY1
import XSf_PrepareSemantic
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotRun
set_option autoImplicit false
noncomputable section
namespace XSf_A3Produced
open AspisR1 AspisR1ClaimPreparedBridge

/-- Whole accepted-prepare LOCAL carrier trace, with semantic/y1/g/inactive/
kappa canonicality all derived from that producing execution. This does not
claim the missing LPs native P6 bridge or full native rejected-run coverage. -/
theorem trace {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hash : H) (out : C.Prepared) (scratch old : Coeff)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem (cview v) hash old=ok (.Ok out,scratch)) :
 ∃ native : LPi_FieldValues.NE,
 LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (arr toClaimE scratch)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back out.kappa) native ∧
 LPi_FieldValues.canonE native ∧ toClaimE out.claim=LPq_Powers.claim native ∧
 FIo_Native.weights.powers 29#usize (XSf_A3Ports.back out.gamma)=ok (arr XSf_A3Ports.back scratch) :=
 XSf_PrepareY1.trace D sem
   (XSf_PrepareSemantic.produced D sem proof semantic y1 v view hash out scratch old run)
   proof semantic y1 v view hash out scratch old run

#print axioms trace
end XSf_A3Produced
end
