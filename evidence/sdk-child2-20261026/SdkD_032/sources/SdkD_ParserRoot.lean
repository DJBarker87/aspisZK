import SdkD_PhysicalRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ParserRoot
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft

/-- Invert one semantic row without reducing the remaining 26 rows. -/
theorem semantic_head (fuel row : Nat) (b : Bytes) (rs : List Bytes)
    (success : semanticRows (fuel+1) row b = some rs) :
    ∃ tail, rs = (b.take 5 ++
      (if 14 ≤ row then expand ((rowShape row).2/32) (slice b 5 ((rowShape row).2/2))
       else slice b 5 (rowShape row).2)) :: tail ∧
      semanticRows fuel (row+1) (b.drop (5 + if 14 ≤ row then (rowShape row).2/2 else (rowShape row).2)) = some tail := by
  cases shape : rowShape row with
  | mk tag size =>
    simp only [semanticRows,shape] at success
    simp only [shape,Prod.snd] at *
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · cases h : semanticRows fuel (row+1)
            (b.drop (5 + if 14 ≤ row then size/2 else size)) with
          | none => simp [h] at success
          | some tail =>
            simp only [h,Option.bind_some,Option.pure_def,Option.some.injEq] at success
            exact ⟨tail,success.symm,h⟩

#print axioms semantic_head
end AspisR1.SdkD_ParserRoot
end
