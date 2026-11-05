import NHU_TransitionCut
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionStep
open FIq_Native
open pool_v1.pair_forest_semantic_terminal
open NHU_TransitionCut

def expected (p : Public) (level carry : Usize) : Result (Array U32 8#usize) :=
 if level<carry then empty_root level else do
 let shifted←p.transition.live_snapshot.next_pair_index >>> level
 let bit←lift (shifted &&& 1#u64)
 if bit=0#u64 then empty_root level
 else Array.index_usize p.transition.live_snapshot.frontier level

def check (p : Public) (level carry : Usize) (next : Result RR) : Result RR :=
 if level=carry ∧ carry<20#usize then next else do
 let want←expected p level carry
 let got←Array.index_usize p.transition.candidate_afterstate.next_frontier level
 let bad←core.array.equality.PartialEqArray.ne field.M31.Insts.CoreCmpPartialEqM31 got want
 if bad then ok (.Err .InvalidAppendTransition) else next

theorem association (p : Public) (iter : R) (carry : Usize) (next : R→Result RR) :
 step p iter carry next=(do
 let (o,r)←core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
 match o with
 | none=>ok (.Ok ())
 | some level=>check p level carry (next r)) := by
 unfold step
 congr 1
 funext pair
 rcases pair with ⟨o,r⟩
 cases o with
 | none=>rfl
 | some level=>
  simp only [Aeneas.Std.uncurry]
  unfold check
  by_cases same : level=carry
  · by_cases small : carry<20#usize
    · conv_rhs => rw [if_pos ⟨same,small⟩]
      rw [if_pos same,if_pos small]
    · conv_rhs => rw [if_neg (fun h=>small h.2)]
      rw [if_pos same,if_neg small]
      unfold expected
      by_cases earlier : level<carry
      · simp only [if_pos earlier,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
      · simp only [if_neg earlier,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  · conv_rhs => rw [if_neg (fun h=>same h.1)]
    rw [if_neg same]
    unfold expected
    by_cases earlier : level<carry
    · simp only [if_pos earlier,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
    · simp only [if_neg earlier,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms association
end AspisR1.NHU_TransitionStep
end
