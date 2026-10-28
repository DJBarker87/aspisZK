import R1Z.PV_AL_SplitBridge
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RL_V233
set_option autoImplicit false
/-- Read-only raw-slice observation: prefix view and suffix view at consumed. -/
def nativeViews (v : Slice U8) : Result (List U8 × List U8) :=
  let nb := v.val.length/64
  let consumed := nb*64
  ok (v.val.take consumed,v.val.drop consumed)
theorem complete (v : Slice U8) :
    nativeViews v=PV_AL_SplitObservation.observe v 64#usize := by
  rw [PV_AL_SplitObservation.positive v 64#usize (by decide)]
  rfl
theorem bounds (n : Nat) : (n/64)*64≤n ∧ n-(n/64)*64<64 := by omega
theorem no_overlap (i j i' j' : Nat) (hj : j<64) (hj' : j'<64)
    (h : i*64+j=i'*64+j') : i=i' ∧ j=j' := by omega
theorem block_coordinate (n i j : Nat) (hi : i<n/64) (hj : j<64) :
    i*64+j<n ∧ i*64+j<(n/64)*64 := by omega
theorem reassembles (v : Slice U8) :
    v.val.take ((v.val.length/64)*64)++v.val.drop ((v.val.length/64)*64)=v.val :=
  List.take_append_drop _ _
theorem nonvacuous : nativeViews (⟨[],by simp⟩ : Slice U8)=ok ([],[]) := rfl
#print axioms complete
#print axioms bounds
#print axioms no_overlap
#print axioms block_coordinate
#print axioms reassembles
#print axioms nonvacuous
end R1Z.PV_RL_V233
