import NKG_HelperCuts
import NKG_InternalChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_InternalPacket
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State)
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
/-- Native K013's universal replies are instantiated with CLOSED dot/round
Results at SAME arguments. No child Result clause is left as a hypothesis. -/
theorem source (s l nativeOut : State)
 (weights : Fin 2 → NKG_HelperCuts.Seven) (constants : Fin 2 → NKG_HelperCuts.Constants7)
 (states : Fin 2 → State) (roundConstants : Fin 2 → NQ) (dotCalls roundCalls : Nat)
 (hs : canonical s) (hl : canonical l)
 (cut : NKG_HelperCuts.Internal s l weights constants
   (fun c=>if c.val=0 then NKG_InternalChoices.even l else NKG_InternalChoices.odd l)
   states (fun c=>if c.val=0 then NKG_InternalChoices.middle s l else NKG_InternalChoices.last s l)
   roundConstants nativeOut dotCalls roundCalls) :
 state_only_poseidon.interpolated_internal_pair s l=ok nativeOut ∧ canonical nativeOut ∧
 decoded nativeOut=R0P.poseidonInterpolatedInternalPair (decoded s) (decoded l) := by
 obtain ⟨out,run,co,value⟩ := NKG_InternalSource.result s l hs hl
 have returned := cut.returned
 change nativeOut=NKG_InternalChoices.last s l at returned
 have same : nativeOut=out := returned.trans (NKG_InternalChoices.value s l out run)
 rw [same]
 exact ⟨run,co,value⟩
#print source
#print axioms source
end AspisR1.NKG_InternalPacket
end
