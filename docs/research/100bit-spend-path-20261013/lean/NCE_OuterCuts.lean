import NCE_OpeningRead

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_OuterCuts
open Aeneas Aeneas.Std NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Child := Nat → Carrier → Program Bytes State (Bool × Carrier)
inductive Next where
  | stop : Carrier → Next
  | call : Nat → Carrier → Next
abbrev Start := Carrier → Nat × Carrier
abbrev Continue := Bool × Carrier → Next
abbrev Finish := Bool × Carrier → Option Nat × Carrier

/-- ONE dispatch/return per phase of the real three-call source structure.
No accepted child, full batch agreement, chosen intermediate execution or
independent successful scratch is a hypothesis. Each return continues from
THAT child result's actual caller carrier, or stops at its first failure.
Initial zero stores and folded-root/Prepared projection are separate cuts. -/
def NCE_Native_ThreeTrees (start : Start) (after0 after1 : Continue) (finish : Finish) : Prop :=
  (∀ s, start s = (0,s)) ∧
  (∀ accepted s, after0 (accepted,s) = if accepted then .call 1 s else .stop s) ∧
  (∀ accepted s, after1 (accepted,s) = if accepted then .call 2 s else .stop s) ∧
  (∀ accepted s, finish (accepted,s) = (if accepted then none else some 2,s))

/-- Fixed native source call order with actual child returns. No callback
is replaced by a successful opaque value; these are the SAME child functions
on both sides of the control theorem below. -/
def program (start : Start) (after0 after1 : Continue) (finish : Finish)
    (child : Child) (s : Carrier) : Program Bytes State (Option Nat × Carrier) :=
  let call0 := start s
  bind (child call0.1 call0.2) fun out0 =>
    match after0 out0 with
    | .stop stopped => .done (some 0,stopped)
    | .call kind1 s1 => bind (child kind1 s1) fun out1 =>
      match after1 out1 with
      | .stop stopped => .done (some 1,stopped)
      | .call kind2 s2 => bind (child kind2 s2) fun out2 => .done (finish out2)

/-- Exact first-error/prefix composition from the narrow native dispatch
facts, allowing every child to reject and preserving all of its reads.
This closes CONTROL only, not any child or root/initialization association. -/
theorem observation (start : Start) (after0 after1 : Continue) (finish : Finish)
    (cut : NCE_Native_ThreeTrees start after0 after1 finish)
    (H : Bytes → State) (child : Child) (s : Carrier) :
    eval H (program start after0 after1 finish child s) =
      let out0 := eval H (child 0 s)
      if out0.2.1 then
        let out1 := eval H (child 1 out0.2.2)
        if out1.2.1 then
          let out2 := eval H (child 2 out1.2.2)
          (out0.1++out1.1++out2.1,((if out2.2.1 then none else some 2),out2.2.2))
        else (out0.1++out1.1,(some 1,out1.2.2))
      else (out0.1,(some 0,out0.2.2)) := by
  unfold program
  rw [cut.1 s]
  simp only [eval_bind]
  cases h0 : eval H (child 0 s) with
  | mk log0 returned0 =>
    rcases returned0 with ⟨accepted0,s0⟩
    rw [cut.2.1 accepted0 s0]
    cases accepted0 with
    | false => simp only [Bool.false_eq_true,if_false,eval,List.append_nil]
    | true =>
      simp only [if_true,eval_bind]
      cases h1 : eval H (child 1 s0) with
      | mk log1 returned1 =>
        rcases returned1 with ⟨accepted1,s1⟩
        rw [cut.2.2.1 accepted1 s1]
        cases accepted1 with
        | false => simp only [Bool.false_eq_true,if_false,eval,List.append_nil]
        | true =>
          simp only [if_true,eval_bind]
          cases h2 : eval H (child 2 s1) with
          | mk log2 returned2 =>
            rcases returned2 with ⟨accepted2,s2⟩
            rw [cut.2.2.2 accepted2 s2]
            simp only [eval,List.append_nil,List.append_assoc]

#print axioms observation
end AspisR1.NCE_OuterCuts
end
