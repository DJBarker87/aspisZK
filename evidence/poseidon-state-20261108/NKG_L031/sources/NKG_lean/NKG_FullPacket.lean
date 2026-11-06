import NKG_HelperCuts
import NKG_FullChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_FullPacket
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State)
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
/-- K014's arbitrary column/round replies are replaced by the complete CLOSED
children at SAME logged operands; source success is derived internally. -/
theorem source (s l : State) (nativeOut : NKG_HelperCuts.Packed)
 (weights : Fin 2 → Array NQ 3#usize) (columns : Fin 2 → Fin 3 → Array U32 16#usize)
 (states constants : Fin 2 → State) (columnCalls roundCalls : Nat)
 (hs : canonical s) (hl : canonical l)
 (cut : NKG_HelperCuts.Full s l weights columns
   (fun c=>if c.val=0 then NKG_FullChoices.even l else NKG_FullChoices.odd l)
   states constants (NKG_FullChoices.middle s l) (NKG_FullChoices.last s l) nativeOut columnCalls roundCalls) :
 state_only_poseidon.interpolated_full_pair_packed s l=ok nativeOut ∧ canonical nativeOut ∧
 decoded nativeOut=fun g=>R0P.poseidonPackingFormula
   ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
   (fun j=>R0P.poseidonInterpolatedFullPair (decoded s) (decoded l) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨out,run,co,value⟩ := NKG_FullSource.result s l hs hl
 have same : nativeOut=out := cut.returned.trans (NKG_FullChoices.value s l out run)
 rw [same]
 exact ⟨run,co,value⟩
#print source
#print axioms source
end AspisR1.NKG_FullPacket
end
