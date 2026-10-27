import XSf_A3Produced
import LPq_CarrierFacts
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotRun
set_option autoImplicit false
noncomputable section
namespace XSf_A3Narrowed
open AspisR1 AspisR1ClaimPreparedBridge

/-- The accepted narrowed execution itself produces the local trace, native
powers carrier, canonical result, and unique local-trace output. LPs full
native P6 / rejected-native-path association remains an external OPEN row. -/
theorem trace {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hash : H) (out : E.Prepared) (scratch old : Coeff)
 (run : XRy_NarrowPrepare.prepare AspisR1Post25Sampler.sampler.low_base_p_digits
   (ed D) (es sem) v hash old=ok (.Ok out,scratch)) :
 ∃ native : LPi_FieldValues.NE,
 LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (arr toClaimE scratch)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back out.kappa) native ∧
 LPi_FieldValues.canonE native ∧ toClaimE out.claim=LPq_Powers.claim native ∧
 FIo_Native.weights.powers 29#usize (XSf_A3Ports.back out.gamma)=ok (arr XSf_A3Ports.back scratch) ∧
 (∀ other, LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (arr toClaimE scratch)
   (XSf_A3Ports.back v.inactive) (XSf_A3Ports.back out.kappa) other → other=native) := by
 have assoc := XSf_A2.reached_prepare AspisR1Post25Sampler.sampler.low_base_p_digits
   (fun _ => rfl) D sem proof semantic y1 v view hash old
 rw [run,map_ok] at assoc
 have actual : AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual
   D sem (cview v) hash old=ok (.Ok (cprepared out),scratch) := assoc.symm
 obtain ⟨native,tr,co,eqn,powers⟩ := XSf_A3Produced.trace D sem proof semantic y1 v view
   hash (cprepared out) scratch old actual
 have hi := XSf_View.inactive proof semantic y1 v view
 have hk := (XSf_ReachedScratch.produced D sem (cview v) hash (cprepared out) scratch old actual).2.1
 refine ⟨native,tr,co,eqn,powers,?_⟩
 intro other ht
 exact LPq_CarrierFacts.native_unique (toClaimDigest D) hi hk ht tr

#print axioms trace
end XSf_A3Narrowed
end
