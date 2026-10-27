import XRy_Powers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_LoopWide
set_option autoImplicit false
namespace XRy_PowersPublic
open AspisR1ClaimPreparedBridge

theorem roundtrip {N : Usize} (a : Array C.E N) :
 mapArray fromClaimE (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray (arr toLoop a)) = a := by
 apply Subtype.ext
 change ((a.val.map toLoop).map _).map fromClaimE = a.val
 rw [List.map_map,List.map_map]
 have hi : ((fromClaimE ∘ AspisR1CurrentPreparedClaim.ClaimPowers.fromPowers) ∘ toLoop : C.E → C.E) = id := by funext x; rfl
 rw [hi,List.map_id]

theorem powers (N : Usize) (x : C.E) (hx : XRy_WideMultiply.Canonical x) :
 XRn_Join_Release.weights.powers N x = AspisR1ClaimPreparedBridge.powersPublic N x := by
 obtain ⟨out,hr,ht⟩ := XRy_Powers.paired N x hx
 rw [hr]
 unfold powersPublic AspisR1CurrentPreparedClaim.ClaimPowers.powers
 have hin : AspisR1CurrentPreparedClaim.ClaimPowers.toPowers (toClaimE x) = toLoop x := rfl
 simp only [hin,ht,bind_tc_ok,roundtrip]

#print axioms roundtrip
#print axioms powers
end XRy_PowersPublic
