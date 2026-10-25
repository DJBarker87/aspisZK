import SdkD_PhysicalRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ParserRoot
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft

/-- One early row; the recursive suffix stays symbolic. -/
theorem semantic_head (fuel row : Nat) (b : Bytes) (rs : List Bytes) (early : row < 14)
    (success : semanticRows (fuel+1) row b = some rs) :
    ∃ tail, rs = (b.take 5 ++ slice b 5 (rowShape row).2) :: tail ∧
      semanticRows fuel (row+1) (b.drop (5 + (rowShape row).2)) = some tail := by
  have late : ¬14 ≤ row := by omega
  cases shape : rowShape row with
  | mk tag size =>
    simp only [semanticRows,shape,late,ite_false,false_and] at success
    simp only [shape,Prod.snd]
    by_cases short : b.length < 5+size
    · simp only [if_pos short] at success; cases success
    · simp only [if_neg short] at success
      by_cases header : b.take 5 ≠ (⟨tag % 256,Nat.mod_lt _ (by decide)⟩ :: le32 size)
      · simp only [if_pos header] at success; cases success
      · simp only [if_neg header,Bool.false_eq_true,if_false] at success
        cases h : semanticRows fuel (row+1) (b.drop (5+size)) with
        | none => simp only [h,Option.bind_none] at success; cases success
        | some tail =>
          simp only [h,Option.bind_some,Option.pure_def,Option.some.injEq] at success
          exact ⟨tail,(Option.some.inj success).symm,rfl⟩

#print axioms semantic_head
end AspisR1.SdkD_ParserRoot
end
