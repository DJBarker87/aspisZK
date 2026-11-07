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
  simp only [FIq_Carriers.mapArray,lowerClaims,arr,List.map_map,Function.comp_def,lower_array,
    LIB_VTerminalCarriers.nativeClaims,LIB_VCarriers.claimsRaw,LIB_VScalarCarriers.array]
  rfl
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

theorem projected (fallback : Value) (a : LIB_VTerminal.Args) (domain : LIB_VTerminal.Domain a) :
    NNG_EmittedCallGraph.resultMap (projectReply fallback)
      (NNG_ModelTerminal.call (fromT9 a.1) (lowerClaims a.2.1) (lowerArray a.2.2.1) (lowerChallenges a.2.2.2)) =
      LIB_VTerminal.model a := by
  unfold NNG_ModelTerminal.call
  rw [native]
  have canonical := LIB_VTerminal.native_good a domain
  unfold LIB_VTerminal.model
  rw [dif_pos domain]
  cases h : LIB_VTerminal.native a with
  | fail e => rfl
  | div => rfl
  | ok reply =>
    cases reply with
    | Err e => rfl
    | Ok q =>
      have hq : FIv_NativeValue.Canon q := by simpa only [h,LIB_VTerminal.Good] using canonical
      change Result.ok (Except.ok (project fallback (raiseQ q))) = Result.ok (Except.ok (LIB_VTerminalCarriers.ofNative q hq))
      rw [←lower_ofNative q hq,project_lower]
#print axioms projected
end AspisR1.NNG_LIBTerminal
