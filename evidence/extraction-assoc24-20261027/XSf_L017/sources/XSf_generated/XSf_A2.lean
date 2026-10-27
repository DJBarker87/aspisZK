import XSf_PrepareClaim
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XSf_A2

theorem reached_prepare (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b=AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (sem : C.Sem H) (proof semantic y1 : Slice U8)
 (v : XRn_Join_Release.verifier.View) (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (hash : H) (old : Array C.E 29#usize) :
 mapR (fun (p : core.result.Result E.Prepared E.Err × Array C.E 29#usize) => (inner cprepared ce p.1,p.2))
   (XRy_NarrowPrepare.prepare low (ed D) (es sem) v hash old) =
 AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual D sem (cview v) hash old := by
 have h := XRy_PreparePowers.prepare low leaf D sem (cview v) hash old
 have hv : eview (cview v)=v := by
   rcases v with ⟨variant,a,b,c,d,e,f,g,h⟩
   cases variant <;> rfl
 rw [hv] at h
 exact h.trans (XSf_PrepareClaim.change_claim D sem (cview v) hash old
   (XSf_View.inactive proof semantic y1 v view))

/-- The whole wide-view/prepare continuation, including Parse, panic,
 divergence and every preparation failure, on the SAME proof and scratch. -/
theorem whole (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b=AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (sem : C.Sem H) (proof semantic y1 : Slice U8)
 (hash : H) (old : Array C.E 29#usize) :
 mapR (fun (p : core.result.Result E.Prepared E.Err × Array C.E 29#usize) => (inner cprepared ce p.1,p.2))
   (do let r ← _root_.verifier.candidate.wide_view proof semantic y1
       match r with
       | .Err e => ok (.Err e,old)
       | .Ok v => XRy_NarrowPrepare.prepare low (ed D) (es sem) v hash old) =
 (do let r ← _root_.verifier.candidate.wide_view proof semantic y1
     match r with
     | .Err e => ok (.Err (ce e),old)
     | .Ok v => AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual D sem (cview v) hash old) := by
 rw [mapR_bind]
 apply (bind_eq_iff _ _ _).mpr
 intro r hr
 cases r with
 | Err e => rfl
 | Ok v => exact reached_prepare low leaf D sem proof semantic y1 v hr hash old

#print axioms reached_prepare
#print axioms whole
end XSf_A2
end
