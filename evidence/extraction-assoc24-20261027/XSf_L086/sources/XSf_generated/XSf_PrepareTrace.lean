import XSf_A3NativePowers
import XSf_A3Trace
import XSf_ReachedScratch
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XSf_PrepareTrace
open AspisR1 AspisR1ClaimPreparedBridge

/-- A3's conditional local trace on the exact output scratch and challenges
of one accepted prepare. The ONLY residual input-domain obligations are the
semantic and y1 ports still being closed by LPs; no native closure is claimed. -/
theorem from_prepare {H : Type} (D : C.D H) (sem : C.Sem H)
 (hs : LPq_ReadPorts.SemCanonical (toClaimSem sem))
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hy : LPq_SelectedDomain.ByteDomain v.y1)
 (hash : H) (out : C.Prepared) (scratch old : XSa_DotRun.Coeff)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem (cview v) hash old=ok (.Ok out,scratch)) :
 ∃ native : LPi_FieldValues.NE,
 LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (arr toClaimE scratch)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back out.kappa) native ∧
 LPi_FieldValues.canonE native ∧ toClaimE out.claim=LPq_Powers.claim native ∧
 FIo_Native.weights.powers 29#usize (XSf_A3Ports.back out.gamma)=ok (arr XSf_A3Ports.back scratch) := by
 obtain ⟨hgamma,hkappa,hg,hpowers,hraw⟩ := XSf_ReachedScratch.produced D sem (cview v) hash out scratch old run
 have hi := XSf_View.inactive proof semantic y1 v view
 obtain ⟨native,tr,co,eqn⟩ := LPq_SelectedDomain.native_result (toClaimSem sem) hs v.y1 hy
   (arr toClaimE scratch) (XSf_A3Ports.weights scratch hg)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back out.kappa) hi hkappa
 have nr := congrFun eqn (toClaimDigest D)
 simp only [LPq_PreparedClaim.program,XSf_A3Ports.roundtrip] at nr
 have source := prepared_success_concrete_claim XRo_Join_Installed.actual.sampling
   D sem (cview v) hash out scratch old run
 have same := core.result.Result.Ok.inj (Result.ok.inj (source.2.symm.trans nr))
 exact ⟨native,tr,co,same,XSf_A3NativePowers.observed out.gamma hgamma scratch hpowers⟩

#print axioms from_prepare
end XSf_PrepareTrace
end
