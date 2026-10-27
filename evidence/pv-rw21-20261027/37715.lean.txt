import R1Z.ProverRw21CellLists
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21CompactValues
open ProverRw21ProtocolOutput ProverRw21ByteLengths ProverCommitValueRange47
open ProverCommitCompact43 ProverCommitCompactSource46 ProverRw21CellLists
open ProverCommitPublish43 (Bytes)

theorem wides_emit {n : Nat} (xs : Fin n → E) :
    wides xs = emit (List.ofFn (fun i => bytes (xs i))) := by
  simp only [wides,emit,List.map_ofFn]
  rfl

theorem chunks_wides {n : Nat} (xs : Fin n → E) :
    chunks (wides xs)=List.ofFn (fun i => bytes (xs i)) := by
  rw [wides_emit,chunks_emit]

theorem high_zero {n : Nat} (xs : Fin n → Q) :
    ∀ c∈chunks (wides (fun i => embed (xs i))), highZero c := by
  rw [chunks_wides]
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact embedded_high_zero _

theorem reference_values {n : Nat} (xs : Fin n → Q) (out : Bytes) :
    referenceValues (wides (fun i => embed (xs i))) out =
      .ok (out ++ (List.ofFn (fun i => quarter (xs i))).flatten) := by
  unfold referenceValues
  rw [wides_length]
  simp only [Nat.mul_mod_left,ne_eq,not_true_eq_false,if_false]
  apply (values_ok _ _ _).mpr
  refine ⟨high_zero xs,?_⟩
  rw [chunks_wides,List.map_ofFn]
  rfl

#print axioms wides_emit
#print axioms chunks_wides
#print axioms high_zero
#print axioms reference_values
end R1Z.ProverRw21CompactValues
