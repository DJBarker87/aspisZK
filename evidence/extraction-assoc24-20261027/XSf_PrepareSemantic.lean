import XSf_PartObserved
import XSf_SemReads
import XSf_ReachedScratch
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotRun
set_option autoImplicit false
noncomputable section
namespace XSf_PrepareSemantic
open AspisR1 AspisR1ClaimPreparedBridge

theorem produced {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hash : H) (out : C.Prepared) (scratch old : Coeff)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem (cview v) hash old=ok (.Ok out,scratch)) : LPq_ReadPorts.SemCanonical (toClaimSem sem) := by
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
 apply XSf_SemReads.canonical sem v.y1
 intro p hp l hl
 have pval : (XRn_Join_usize p).val=p := XRy_ClaimSelect.usize_value p (by omega)
 obtain ⟨i,value,hib,hinc,hdot,hcell⟩ := hparts (XRn_Join_usize p) (by rw [pval]; omega)
 exact XSf_PartObserved.typed_reads (toClaimDigest D) sem v.y1 scratch hg p (by omega) value hdot l hl

#print axioms produced
end XSf_PrepareSemantic
end
