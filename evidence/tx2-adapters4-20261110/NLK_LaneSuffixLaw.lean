import NLK_LaneFold
set_option autoImplicit false
noncomputable section
namespace NLK_LaneSuffixLaw
open Aeneas Aeneas.Std Result AspisR1
open NKP_LaneCuts
abbrev Lane := NLA_LaneAssemble.Lane
abbrev PE := NKF_BoxModel.PE
attribute [local instance] Classical.propDecidable
/-- Reviewed per-window suffix proposition. This is a LOCAL stage certificate,
not an assumed whole invocation equation. Its native association requires ALL
scalar/root/frontier/owner controls of NLK_lane_suffix, not a variant-only cut. -/
def Cut (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (allocated : Nat) (out : core.result.Result (NKY_BoxAction.Owned Lane) PE) : Prop :=
 match out with
 | .Err e => next.val=0 ∧ root≠emptyRoot ∧ e=.InvalidAccountData
 | .Ok box => (next.val≠0 ∨ root=emptyRoot) ∧
   NKF_LaneConstructor.Fields (NKP_LaneCarrier.make bump master lane next root state) box.value ∧
   box.owner=allocated

/-- Reconstruct every field and the exact error before using the allocator
interpretation. No success premise is retained. -/
theorem value (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (allocated : Nat) (out : core.result.Result (NKY_BoxAction.Owned Lane) PE)
 (cut : Cut bump master lane next root emptyRoot state allocated out) :
 NKY_BoxCarrier.erase out =
 (NKP_LaneCompletion.finish bump master lane next root emptyRoot (.Ok (),state,[])).1 := by
 cases out with
 | Err e =>
   rw [NKP_LaneCompletion.rejected_root bump master lane next root emptyRoot state [] cut.1 cut.2.1]
   exact congrArg core.result.Result.Err cut.2.2
 | Ok box =>
   rw [NKP_LaneCompletion.constructed bump master lane next root emptyRoot state [] cut.1]
   exact congrArg core.result.Result.Ok (NKP_LaneCarrier.returned bump master lane next root state box.value cut.2.1)

/-- Arbitrary Reservation and the allocator's partial post are consumed at
THIS720-byte Box site. The same native owner is returned, never a replacement
carrier. Abort/div and exhaustion remain distinct from returning Err. -/
theorem owned {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root emptyRoot : Node) (state : Frontier)
 (allocated : Nat) (out : core.result.Result (NKY_BoxAction.Owned Lane) PE)
 (cut : Cut bump master lane next root emptyRoot state allocated out) :
 NKY_BoxCarrier.native allocator before 720 reservation out =
 NKY_BoxAction.run allocator before 720 reservation allocated
  (ok (NKP_LaneCompletion.finish bump master lane next root emptyRoot (.Ok (),state,[])).1) := by
 have owner : NKY_BoxCarrier.Owner allocated out := by
  cases out with
  | Err e => trivial
  | Ok box => exact cut.2.2
 rw [NKY_BoxCarrier.association allocator before 720 reservation allocated out owner]
 rw [value bump master lane next root emptyRoot state allocated out cut]

#print value
#print axioms value
#print owned
#print axioms owned
end NLK_LaneSuffixLaw
