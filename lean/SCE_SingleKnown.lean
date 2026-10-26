import SCE_SingleRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleKnown
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass

/-- The suffix produced by repeating the SAME source verifier contains only
already recorded addresses. No claim of literal-log equality is needed. -/
theorem known (rust : Verifier) (P : Prover) (H : Bytes → State) :
    let v := eval H (originalWith rust P)
    ∀ a ∈ (eval H (rust v.2.1)).1.map Prod.fst, a ∈ v.1.map Prod.fst := by
  rw [F3T_TwoPass.original_eval]
  dsimp only
  intro a member
  simp only [List.map_append,List.mem_append]
  exact Or.inr member

theorem consistent (rust : Verifier) (P : Prover) (H : Bytes → State) :
    let v := eval H (originalWith rust P)
    ∀ q ∈ v.1 ++ (eval H (rust v.2.1)).1, q.2 = H q.1 := by
  dsimp only
  intro q member
  rcases List.mem_append.mp member with first | second
  · exact FS.eval_consistent H (originalWith rust P) q first
  · exact FS.eval_consistent H (rust (eval H (originalWith rust P)).2.1) q second

#print axioms known
#print axioms consistent
end AspisR1.SCE_SingleKnown
end
