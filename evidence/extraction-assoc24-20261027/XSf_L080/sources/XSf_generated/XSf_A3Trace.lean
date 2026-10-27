import XSf_A3Ports
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XSf_A3Trace
open AspisR1 AspisR1ClaimPreparedBridge

/-- Conditional local trace theorem only. SemCanonical and ByteDomain are
explicit remaining caller obligations; this does NOT close LPs native P6. -/
theorem construct {H : Type} (D : C.D H) (sem : C.Sem H)
 (hs : LPq_ReadPorts.SemCanonical (toClaimSem sem))
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hy : LPq_SelectedDomain.ByteDomain v.y1)
 (t t1 t2 : C.T H) (gamma kappa : C.E) (bytes : Array U8 32#usize)
 (hg : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D t 27#u8 v.y1 true=ok (gamma,t1))
 (hb : XRo_Join_Installed.actual.sampling.toBytes v.inactive=ok bytes)
 (hk : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2))
 (g : XSa_DotRun.Coeff) (hp : powersPublic 29#usize gamma=ok g) :
 ∃ out : LPi_FieldValues.NE,
 LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (arr toClaimE g)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back kappa) out ∧
 LPi_FieldValues.canonE out ∧
 XRo_Join_Installed.actual.claim D sem v.y1 v.inactive g kappa=ok (.Ok (fromClaimE (LPq_Powers.claim out))) ∧
 XRo_Join_PreparedBoundaries.cachedClaim D sem v.y1 v.inactive g kappa=ok (.Ok (fromClaimE (LPq_Powers.claim out))) := by
 have hi := XSf_View.inactive proof semantic y1 v view
 have hkc := XSf_Reached.kappa D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
 have hgc := (XSf_A3Powers.observed_weights D t t1 v.y1 gamma g hg hp).1
 obtain ⟨out,tr,co,eqn⟩ := LPq_SelectedDomain.native_result (toClaimSem sem) hs v.y1 hy
   (arr toClaimE g) (XSf_A3Ports.weights g hgc)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back kappa) hi hkc
 have run := congrFun eqn (toClaimDigest D)
 simp only [LPq_PreparedClaim.program,XSf_A3Ports.roundtrip] at run
 have actual : XRo_Join_Installed.actual.claim D sem v.y1 v.inactive g kappa=
   ok (.Ok (fromClaimE (LPq_Powers.claim out))) := by
   rw [XRo_Join_Installed.cached_claim_slot]
   unfold claimPublic
   rw [run,bind_tc_ok]
 exact ⟨out,tr,co,actual,(XSf_A3Powers.claim_at_call D sem proof semantic y1 v view
   t t1 t2 gamma kappa bytes hg hb hk g hp).trans actual⟩

#print axioms construct
end XSf_A3Trace
end
