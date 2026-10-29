import R1Z.PV_RunJoin_InactiveCell48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveFinite48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_InactiveCell48 (W Source)

def run : Nat → Slice W → ProverCommitWeightsStorage53.State → Source → Usize → Result Source
  | 0,_,_,sum,_ => ok sum
  | n+1,q,state,sum,row => do
    let next ← PV_RunJoin_InactiveCell48.step q state sum row
    run n q state next (Usize.wrapping_add row 1#usize)

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Slice W) (w : PV_RunJoin_WeightCarrier46.W)
    (hs : w.variant=.S2) (n : Nat) (sum : Source) (row : Usize) :
    @PV_RunJoin_InactiveThread48.phase (types base) (selected base heap box ops) q w n (fromW sum) row=
      mapResult fromW (run n q (PV_RunJoin_WeightCarrier46.state w) sum row) := by
  induction n generalizing sum row with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_InactiveThread48.phase,run]
    rw [PV_RunJoin_InactiveCell48.complete base heap box ops q w hs sum row,
      PV_RunJoin_OpeningResult48.bind_map,PV_RunJoin_OpeningResult48.map_after]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    exact ih next _
#print axioms complete
end R1Z.PV_RunJoin_InactiveFinite48
