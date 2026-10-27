import XSf_Y1Produced
import XSf_PrepareTrace
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotRun
set_option autoImplicit false
noncomputable section
namespace XSf_PrepareY1
open AspisR1 AspisR1ClaimPreparedBridge

theorem produced {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hash : H) (out : C.Prepared) (scratch old : Coeff)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem (cview v) hash old=ok (.Ok out,scratch)) : LPq_SelectedDomain.ByteDomain v.y1 := by
 have hi := XSf_View.inactive proof semantic y1 v view
 have hk := (XSf_ReachedScratch.produced D sem (cview v) hash out scratch old run).2.1
 have hg := (XSf_ReachedScratch.produced D sem (cview v) hash out scratch old run).2.2.1
 have source := prepared_success_concrete_claim XRo_Join_Installed.actual.sampling
   D sem (cview v) hash out scratch old run
 obtain ⟨final,hzero,hparts,hcanonical,hpolynomial⟩ :=
   AspisR1CurrentPreparedClaim.ClaimParts.successful_concrete_claim_kappa_polynomial
     AspisR1EbyKPushDecodedProductUpdate.QRaw (toClaimDigest D) (toClaimSem sem) v.y1
     (toClaimE v.inactive) (toClaimE out.kappa) (toClaimE out.claim)
     (arr toClaimE scratch) hk hi source.2
 obtain ⟨i,value,hib,hinc,hdot,hcell⟩ := hparts 5#usize (by scalar_tac)
 exact XSf_Y1Produced.dot_domain (toClaimDigest D) sem v.y1 scratch hg value hdot

theorem trace {H : Type} (D : C.D H) (sem : C.Sem H)
 (hs : LPq_ReadPorts.SemCanonical (toClaimSem sem))
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
 XSf_PrepareTrace.from_prepare D sem hs proof semantic y1 v view
   (produced D sem proof semantic y1 v view hash out scratch old run) hash out scratch old run

#print axioms produced
#print axioms trace
end XSf_PrepareY1
end
