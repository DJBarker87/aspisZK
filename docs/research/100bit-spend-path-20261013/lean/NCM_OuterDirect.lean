import NCM_OuterObservation

set_option autoImplicit false
namespace AspisR1.NCM_OuterDirect
open NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Direct observation of an actual child interpreter. Stored prefix removal
belongs to the observer; it never reissues a digest or replays a request. -/
abbrev Child := Nat → Carrier → NCE_FirstFailure.Log × Bool × Carrier

def execute (start : NCE_OuterCuts.Start) (after0 after1 : NCE_OuterCuts.Continue)
    (finish : NCE_OuterCuts.Finish) (child : Child) (s : Carrier) :
    NCE_FirstFailure.Log × Option Nat × Carrier :=
  let dispatched := start s
  let out0 := child dispatched.1 dispatched.2
  match after0 out0.2 with
  | .stop stopped => (out0.1,some 0,stopped)
  | .call kind1 next1 =>
    let out1 := child kind1 next1
    match after1 out1.2 with
    | .stop stopped => (out0.1++out1.1,some 1,stopped)
    | .call kind2 next2 =>
      let out2 := child kind2 next2
      (out0.1++out1.1++out2.1,finish out2.2)

/-- The same native phase control applies to already-observed child returns.
This interpretation observes each child ONCE; it does not manufacture Program
asks from its returned log. -/
theorem control (start : NCE_OuterCuts.Start) (after0 after1 : NCE_OuterCuts.Continue)
    (finish : NCE_OuterCuts.Finish)
    (cut : NCE_OuterCuts.NCE_Native_ThreeTrees start after0 after1 finish)
    (child : Child) (s : Carrier) :
    execute start after0 after1 finish child s =
      let out0 := child 0 s
      if out0.2.1 then
        let out1 := child 1 out0.2.2
        if out1.2.1 then
          let out2 := child 2 out1.2.2
          (out0.1++out1.1++out2.1,(if out2.2.1 then none else some 2),out2.2.2)
        else (out0.1++out1.1,some 1,out1.2.2)
      else (out0.1,some 0,out0.2.2) := by
  unfold execute
  rw [cut.1 s]
  dsimp only
  cases first : child 0 s with
  | mk log0 out0 =>
    rcases out0 with ⟨accepted0,s0⟩
    rw [cut.2.1 accepted0 s0]
    cases accepted0 with
    | false => simp only [Bool.false_eq_true,if_false]
    | true =>
      simp only [if_true]
      try dsimp only
      cases second : child 1 s0 with
      | mk log1 out1 =>
        rcases out1 with ⟨accepted1,s1⟩
        rw [cut.2.2.1 accepted1 s1]
        cases accepted1 with
        | false => simp only [Bool.false_eq_true,if_false]
        | true =>
          simp only [if_true]
          try dsimp only
          cases third : child 2 s1 with
          | mk log2 out2 =>
            rcases out2 with ⟨accepted2,s2⟩
            rw [cut.2.2.2 accepted2 s2]

#print axioms control
end AspisR1.NCM_OuterDirect
