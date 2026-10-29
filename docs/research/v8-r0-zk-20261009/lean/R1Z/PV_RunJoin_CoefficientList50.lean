import R1Z.PV_RunJoin_CoefficientActualCell50
import R1Z.PV_RunJoin_CoefficientsThread45
import R1Z.PV_RunJoin_ClaimList48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientList50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_CoefficientActualCell50 (Column permuted)

def run : List Column → alloc.vec.Vec Column → Result (alloc.vec.Vec Column)
  | [],out => ok out
  | q::tail,out => do
    let next ← alloc.vec.Vec.push out (permuted q)
    run tail next

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (messages : Slice Column) (n : Nat) (out : alloc.vec.Vec Column) (lane : Usize)
    (small : messages.length≤14336) (rank : lane.val+n=messages.length) :
    @PV_RunJoin_CoefficientsThread45.phase (types base) (selected base heap box ops) .S2 messages n out lane=
      run (messages.val.drop lane.val) out := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have len : messages.val.length=messages.length := rfl
  induction n generalizing out lane with
  | zero =>
    rw [List.drop_eq_nil_of_le (show messages.val.length≤lane.val by omega)]
    rfl
  | succ n ih =>
    have hi : lane.val<messages.val.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    simp only [PV_RunJoin_CoefficientsThread45.phase,PV_RunJoin_CoefficientsThread45.step,
      PV_RunJoin_ClaimList48.read messages lane hi,bind_tc_ok,run]
    rw [PV_RunJoin_CoefficientActualCell50.complete base heap box ops]
    simp only [bind_tc_ok]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    rw [ih next _ (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega)]
    rw [PV_RunJoin_MergeLoop35.increment lane (by omega)]
#print axioms run
#print axioms complete
end R1Z.PV_RunJoin_CoefficientList50
