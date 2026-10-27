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
        have same : (⟨stored,rs⟩ : Parsed) = p := Option.some.inj success
        subst p
        exact call

theorem row2 (b : Bytes) (rs : List Bytes) (success : semanticRows 27 0 b = some rs) :
    (rs[2]?.getD []).drop 5 = slice (b.drop 10) 5 32 := by
  obtain ⟨r1,h0,s0⟩ := SdkD_ParserRoot.semantic_head 26 0 b rs (by decide) success
  have s0' : semanticRows 26 1 (b.drop 5) = some r1 := by
    simpa only [rowShape,↓reduceIte,Prod.snd,Nat.add_zero] using s0
  obtain ⟨r2,h1,s1⟩ := SdkD_ParserRoot.semantic_head 25 1 (b.drop 5) r1 (by decide) s0'
  have s1' : semanticRows 25 2 (b.drop 10) = some r2 := by
    simpa only [rowShape,↓reduceIte,Prod.snd,Nat.add_zero,List.drop_drop] using s1
  obtain ⟨r3,h2,s2⟩ := SdkD_ParserRoot.semantic_head 24 2 (b.drop 10) r2 (by decide) s1'
  have len : (b.drop 10).length ≥ 5 := by
    unfold semanticRows at s1'
    simp only [rowShape,↓reduceIte,Prod.snd] at s1'
    split at s1'
    · cases s1'
    · omega
  rw [h0,h1,h2]
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    rowShape,↓reduceIte,Prod.snd,List.drop_append,List.drop_take,List.drop_self,
    List.nil_append,List.length_take,Nat.min_eq_left len,Nat.sub_self,List.drop_zero]

#print axioms rows
#print axioms row2
end AspisR1.SdkD_ParserRows
end
