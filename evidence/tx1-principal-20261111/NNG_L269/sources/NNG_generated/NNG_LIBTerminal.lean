import NNG_ModelTerminal
import NNG_LIBRecords
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBTerminal
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays NNG_ModelTerminal
open AspisR1.NMT_Transport (arr)

theorem lower_scalar (q : Value) : lowerQ (lower q) = LIB_VTerminalCarriers.scalar q := by
  unfold lowerQ lower
  rw [fromT1_inverse]
  rfl
#print axioms lower_scalar

theorem lower_array {n : Usize} (a : Array Value n) :
    FIq_Carriers.mapArray lowerQ (lowerArray a) = LIB_VTerminalCarriers.nativeArray a := by
  apply Subtype.ext
  simp only [FIq_Carriers.mapArray,lowerArray,arr,LIB_VTerminalCarriers.nativeArray,
    LIB_VScalarCarriers.array,List.map_map,Function.comp_def,lower_scalar]
  rfl
#print axioms lower_array

theorem lower_claims (a : LIB_VCarriers.Claims) :
    FIq_Carriers.mapArray (FIq_Carriers.mapArray lowerQ) (lowerClaims a) = LIB_VTerminalCarriers.nativeClaims a := by
  apply Subtype.ext
  change (a.val.map lowerArray).map (FIq_Carriers.mapArray lowerQ) =
    (a.val.map LIB_VCarriers.k29Raw).map (FIq_Carriers.mapArray FIq_Carriers.toQ)
  rw [List.map_map,List.map_map]
  apply List.map_congr_left
  intro row _
  exact lower_array row
#print axioms lower_claims

theorem lower_challenges (a : LIB_VCarriers.Challenges) :
    toT3 (lowerChallenges a) = LIB_VCarriers.challengesRaw a := by
  cases a
  simp only [toT3,lowerChallenges,lower,fromT1_inverse,LIB_VCarriers.challengesRaw]
  congr 1
  rw [←NNG_LIBRecords.raise_array]
  exact AspisR1.NMT_Transport.arr_inverse fromT1 toT1 fromT1_inverse _
#print axioms lower_challenges

theorem native (a : LIB_VTerminal.Args) :
    NNG_ModelTerminal.native (fromT9 a.1) (lowerClaims a.2.1) (lowerArray a.2.2.1) (lowerChallenges a.2.2.2) =
      LIB_VTerminal.native a := by
  unfold NNG_ModelTerminal.native LIB_VTerminal.native
  rw [fromT9_inverse,lower_claims,lower_array,lower_challenges]
  rfl
#print axioms native

def projectReply (fallback : Value) : core.result.Result Q NNG_ModelTerminal.Error → Except Unit Value
 | .Ok q => .ok (project fallback q) | .Err _ => .error ()

theorem lower_ofNative (q : NativeQ) (h : FIv_NativeValue.Canon q) :
    lower (LIB_VTerminalCarriers.ofNative q h) = raiseQ q := by
  cases q
  rfl
#print axioms lower_ofNative

theorem project_lift (fallback : Value)
    (r : Result (core.result.Result NativeQ NativeError)) (good : LIB_VTerminal.Good r) :
    NNG_EmittedCallGraph.resultMap (projectReply fallback)
      (NMP_ResultTransport.outer (NMP_ResultTransport.inner raiseQ raiseError) r) = LIB_VTerminal.liftRaw r good := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok reply =>
    cases reply with
    | Err e => rfl
    | Ok q =>
      change Result.ok (Except.ok (project fallback (raiseQ q))) = Result.ok (Except.ok (LIB_VTerminalCarriers.ofNative q good))
      rw [←lower_ofNative q good,project_lower]
#print axioms project_lift

theorem projected (fallback : Value) (a : LIB_VTerminal.Args) (domain : LIB_VTerminal.Domain a) :
    NNG_EmittedCallGraph.resultMap (projectReply fallback)
      (NNG_ModelTerminal.call (fromT9 a.1) (lowerClaims a.2.1) (lowerArray a.2.2.1) (lowerChallenges a.2.2.2)) =
      LIB_VTerminal.model a := by
  unfold NNG_ModelTerminal.call
  rw [native]
  have canonical := LIB_VTerminal.native_good a domain
  unfold LIB_VTerminal.model
  rw [dif_pos domain]
  exact project_lift fallback (LIB_VTerminal.native a) canonical
#print axioms projected
end AspisR1.NNG_LIBTerminal
