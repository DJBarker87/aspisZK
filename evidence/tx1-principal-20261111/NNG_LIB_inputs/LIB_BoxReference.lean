import LIB_BoxSpec
import LIB_Carriers
import NKY_BoxSource
import NND_Carrier
set_option autoImplicit false
namespace LIB_BoxReference
open Aeneas Aeneas.Std AspisR1
/-- Owner/state erasure for a single source Box site. The infallible site's
reply is quantified independently of Env's fallible try_reserve reply. -/
def allocator : S2W_D189Wrappers.Allocator Unit :=
 ⟨fun _ _ => .ok (),fun _ => .ok ()⟩
def returns (r : NP6_StdModel.Reservation) : Bool :=
 match r with | .Ok _ => true | .Err _ => false
def value {T : Type} (x : core.result.Result (NKY_BoxAction.Owned T) NKY_BoxAction.PE × Unit) :
 Except RSL.ProgramError T :=
 match x.1 with | .Ok b => .ok b.value | .Err e => .error (NND_Carrier.error e)
def observation {T : Type}
 (m : Result (core.result.Result (NKY_BoxAction.Owned T) NKY_BoxAction.PE × Unit)) :=
 LIB_Carriers.resultObs value [] m
/-- The CLOSED wrapper reference retains exactly the decoder result or the
single named Box abort, with no allocation-success premise. -/
theorem normalized {T : Type} (d : core.result.Result T NKY_BoxAction.PE)
 (r : NP6_StdModel.Reservation) (n owner : Nat) :
 observation (NKY_BoxAction.run allocator () n r owner (.ok d)) =
 LIB_BoxSpec.observe (returns r) (NND_Carrier.reply id d) := by
 cases d with
 | Err e => rfl
 | Ok x => cases r with
   | Err e => rfl
   | Ok u => cases u; rfl
theorem member {T : Type} (d : core.result.Result T NKY_BoxAction.PE)
 (r : NP6_StdModel.Reservation) (n owner : Nat) (env : RSL.Env) :
 LIB_BoxSpec.law (NND_Carrier.reply id d) env
  (observation (NKY_BoxAction.run allocator () n r owner (.ok d))) := by
 rw [normalized]
 exact LIB_BoxSpec.member _ _ env
/-- Native/emitted-copy association stays separate from the graph law.
These are exactly the supplying CLOSED roots, with all window hypotheses visible. -/
abbrev master_source := @NKY_BoxSource.master
abbrev checkpoint_source := @NKY_BoxSource.checkpoint
#print axioms normalized
#print axioms member
#print axioms master_source
#print axioms checkpoint_source
end LIB_BoxReference
