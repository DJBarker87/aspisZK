import NJV_NativeEntry

set_option autoImplicit false
noncomputable section
namespace NJV_AdoptedObservation
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1.MultiproofConePhysicalTransport

/-- Chronological byte requests and replies, preserving repeated queries. -/
def history (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) :=
 (events.map (fun e => (NJP_RequestTransport.address e.1,encode e.2))).map
   (fun e => (flatten e.1,decodeState e.2))

/-- Native G to this adopted endpoint at this entry. Full Result and every
buffer coordinate are transported before projecting any Bool. -/
theorem returning (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (s : reference.Scratch) (zero : s.«at»=0#usize) (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
       root physical s events out) :
 let adopted := eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)
 (adopted.1,ok (NJP_CohortReturning.answer adopted.2))=(history events,ok out) := by
 dsimp only
 have source := NJV_Entry.adopted H root physical s zero bytes
 rw [transport_observation] at source
 have nativeObs := NJV_NativeEntry.observation (rawOracle H) root physical s events out native
 dsimp only at nativeObs
 have sourceLogs := congrArg Prod.fst source
 have sourceReturn := congrArg Prod.snd source
 have nativeLogs := congrArg Prod.fst nativeObs
 have nativeReturn := congrArg Prod.snd nativeObs
 dsimp only at sourceLogs sourceReturn nativeLogs nativeReturn
 rw [sourceReturn] at nativeReturn
 simp only [mapResult] at nativeReturn
 apply Prod.ext
 · exact sourceLogs.symm.trans (congrArg (List.map (fun e => (flatten e.1,decodeState e.2))) nativeLogs)
 · exact nativeReturn

#print returning
#print axioms returning
end NJV_AdoptedObservation
end
