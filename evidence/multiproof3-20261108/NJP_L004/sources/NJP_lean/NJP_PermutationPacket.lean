import NJP_ControllerTrace
import NJP_FieldEncoding

set_option autoImplicit false
noncomputable section
namespace NJP_PermutationPacket
open Aeneas Aeneas.Std Result
abbrev State := NJE_RoundTrace.State

def model (input : State) : State := fun i =>
 NJP_FieldEncoding.word (R0P.poseidonPermutation (NJE_RoundTrace.cast input) i)

/-- Complete raw mutable state and returning unit, at the deployed no-op
callback instance. Native association is K006/K007, K008/K009 plus the NJE
arbitrary-prestate body cuts, combined under (ad). -/
theorem TX1_306 (input : State) (states : Fin 23 → State)
    (control : Fin 22 → Nat × NJA_Trace.Kind)
    (cut : NJP_ControllerTrace.Cut input states control) :
    states (Fin.last 22)=model input ∧
    (ok ((),states (Fin.last 22)) : Result (Unit × State))=ok ((),model input) ∧
    ∀ r, ((NJE_RoundTrace.observed input states r).round,
      (NJE_RoundTrace.observed input states r).kind)=control r := by
 obtain ⟨canonical,value,_,descriptors⟩ := NJP_ControllerTrace.result input states control cut
 have raw : states (Fin.last 22)=model input := by
   funext i
   exact NJP_FieldEncoding.unique _ _ (canonical i) (congrFun value i)
 exact ⟨raw,congrArg (fun s => (ok ((),s) : Result (Unit × State))) raw,descriptors⟩

theorem model_domain (input : State) : NJE_RoundTrace.Canonical (model input) :=
 fun i => NJP_FieldEncoding.canonical _

#print TX1_306
#print axioms TX1_306
#print model_domain
#print axioms model_domain
end NJP_PermutationPacket
end
