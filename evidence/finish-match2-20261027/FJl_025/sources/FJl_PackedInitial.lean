import Port5Q1_Parsed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PackedInitial
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
/-- SAME literal C1 packed bytes, including duplicate indices. The indexed
recovery coherence input is explicit; this lemma does not derive it. -/
theorem c1 (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 0 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 0 pos)) (j : Fin 22) :
    packed parsed q 0 (q j).val=some ((opening parsed j.val).take 480) := by
  have h := OraclePortPackedChoiceC4.packed_agrees parsed q 0 recovered authenticated j.val j.isLt
  rw [authenticated j.val j.isLt] at h
  have jmod : (⟨j.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [index,jmod,show (0:Nat)≠2 by decide,if_false,
    OraclePortPackedChoiceC4.payload,ite_true] using h
/-- SAME literal C2 packed bytes; source/model identity is kept visible. -/
theorem c2 (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 1 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 1 pos)) (j : Fin 22) :
    packed parsed q 1 (q j).val=some (slice (opening parsed j.val) 480 128) := by
  have h := OraclePortPackedChoiceC4.packed_agrees parsed q 1 recovered authenticated j.val j.isLt
  rw [authenticated j.val j.isLt] at h
  have jmod : (⟨j.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [index,jmod,show (1:Nat)≠2 by decide,show (1:Nat)≠0 by decide,if_false,
    OraclePortPackedChoiceC4.payload,ite_true] using h
#print axioms c1
#print axioms c2
end AspisR1.FJl_PackedInitial
end
