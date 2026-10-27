import PSem_Expand
import MultiproofConeCanonicalAppend
set_option autoImplicit false
namespace AspisR1.PSem_Canonical
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open MultiproofConeExpandModel MultiproofConeCanonicalAppend

theorem little_zeros (n : Nat) : little (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte))=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,little,List.foldr_cons] at *;rw [ih];rfl

theorem canonical_zeros (n : Nat) (aligned : n%4=0) : canonical (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte)) := by
  refine ⟨by simpa only [List.length_replicate] using aligned,?_⟩
  intro j _
  simp only [slice,List.drop_replicate,List.take_replicate,little_zeros]
  decide

theorem canonical_expansion (n : Nat) (b : Bytes) (length : b.length=16*n) :
    canonical (expand n b) ↔ canonical b := by
  induction n generalizing b with
  | zero =>
    have empty : b=[] := List.eq_nil_of_length_eq_zero (by omega)
    simp [empty,expand,canonical]
  | succ n ih =>
    have enough : 16 ≤ b.length := by omega
    have firstLength : (b.take 16).length=16 := by rw [List.length_take,Nat.min_eq_left enough]
    have restLength : (b.drop 16).length=16*n := by rw [List.length_drop];omega
    rw [expand_step,canonical_append _ _ (by rw [List.length_append,firstLength,List.length_replicate] <;> decide),
      canonical_append _ _ (by rw [firstLength] <;> decide),
      ih _ restLength,canonical_take_drop b 16 (by decide) enough]
    simp only [canonical_zeros 16 (by decide),and_true]

#print axioms little_zeros
#print axioms canonical_zeros
#print axioms canonical_expansion
end AspisR1.PSem_Canonical
