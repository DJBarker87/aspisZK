import RPu_FIv_Arithmetic
import RPu_FIq_Native09
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev Capture := pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure
abbrev callback := pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31

theorem value (c last : Capture) (acc bit out : NQ) (ha : Canon acc) (hb : Canon bit)
    (success : callback.call_mut c (acc,bit)=ok (out,last)) :
    Canon out ∧ decode out=(decode acc+decode acc)+decode bit ∧ last=c := by
  simp only [callback,pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut] at success
  obtain ⟨double,hd,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨result,hr,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj success)
  have vd := FIv_NativeValue.add acc acc double ha ha hd
  have vr := FIv_NativeValue.add double bit result vd.1 hb hr
  exact ⟨vr.1,by rw [vr.2,vd.2],rfl⟩
#print axioms value
end AspisR1.FIx_ReconstructStep
end
