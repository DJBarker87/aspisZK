import SdkD_ParserRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ParserRows
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

theorem rows (stored : Bytes) (p : Parsed) (success : parse stored = some p) :
    semanticRows 27 0 (slice p.wire 48 6983) = some p.semantic := by
  unfold parse at success
  split at success
  · cases success
  · split at success
    · cases success
    · cases call : semanticRows 27 0 (slice stored 48 6983) with
      | none => simp [call] at success
      | some rs =>
        rw [call] at success
        have same : (⟨stored,rs⟩ : Parsed) = p := Option.some.inj success
        subst p
        exact call

theorem row2 (b : Bytes) (rs : List Bytes) (success : semanticRows 27 0 b = some rs) :
    (rs[2]?.getD []).drop 5 = slice (b.drop 10) 5 32 := by
  obtain ⟨r1,h0,s0⟩ := SdkD_ParserRoot.semantic_head 26 0 b rs (by decide) success
  have s0' : semanticRows 26 1 (b.drop 5) = some r1 := by
    simpa [rowShape] using s0
  obtain ⟨r2,h1,s1⟩ := SdkD_ParserRoot.semantic_head 25 1 (b.drop 5) r1 (by decide) s0'
  have s1' : semanticRows 25 2 (b.drop 10) = some r2 := by
    simpa [rowShape,List.drop_drop] using s1
  obtain ⟨r3,h2,s2⟩ := SdkD_ParserRoot.semantic_head 24 2 (b.drop 10) r2 (by decide) s1'
  have len : (b.drop 10).length ≥ 5 := by
    have enough : ¬(b.drop 10).length < 37 := by
      intro bad
      have bad' : (b.drop 10).length < 5 + (if 14 ≤ (2:Nat) then (rowShape 2).2/2 else (rowShape 2).2) := by
        simpa [rowShape] using bad
      rw [semanticRows] at s1'
      simp only [bad',if_true] at s1'
      cases s1'
    omega
  rw [h0,h1,h2]
  change ((b.drop 10).take 5 ++ slice (b.drop 10) 5 32).drop 5 = _
  have lengthPrefix : ((b.drop 10).take 5).length = 5 := by
    rw [List.length_take]
    exact Nat.min_eq_left len
  exact List.drop_left' lengthPrefix

#print axioms rows
#print axioms row2
end AspisR1.SdkD_ParserRows
end
