import RRActualScalarTraceBoundsM10

/-! Concatenate actual occurrence lists from eager decoder batches. Repeated
operands are retained as repeated jobs, with no deduplication of failed work. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarBatchJobsM10
open CompPoly GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10 RawExtractorCostLedger
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def flatten {I : Type} (indices : List I) (calls : I → List (Call K)) : List (Call K) :=
  indices.flatMap calls

theorem length {I : Type} (indices : List I) (calls : I → List (Call K)) (N : Nat)
    (h : ∀ i ∈ indices, (calls i).length ≤ N) :
    (flatten indices calls).length ≤ indices.length*N := by
  induction indices with
  | nil => simp only [flatten,List.flatMap_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons i xs ih =>
    have hh := h i List.mem_cons_self
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa only [flatten,List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using
      Nat.add_le_add hh ht

theorem bounded {I : Type} (indices : List I) (calls : I → List (Call K)) (D q : Nat)
    (h : ∀ i ∈ indices, ∀ c ∈ calls i, Bounded D q c) :
    ∀ c ∈ flatten indices calls, Bounded D q c := by
  intro c hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  exact h i hi c hc

theorem jobs {I : Type} (indices : List I) (calls : I → List (Call K)) (D q N : Nat)
    (hl : ∀ i ∈ indices, (calls i).length ≤ N)
    (hb : ∀ i ∈ indices, ∀ c ∈ calls i, Bounded D q c) :
    ∃ j : Jobs K, j.Bounded (D+1) (q+1) (indices.length*N) := by
  have hs := bounded indices calls D q hb
  have hj := GSScalarJobsM10.bounded D q _ hs
  have hc := length indices calls N hl
  exact ⟨GSScalarJobsM10.ofCalls D q _ hs,
    ⟨hj.gcd_count.trans hc,hj.division_count.trans hc,hj.power_count.trans hc,
      hj.gcd_sizes,hj.division_sizes,hj.power_bits⟩⟩

#print axioms length
#print axioms bounded
#print axioms jobs
end AspisR1.GSScalarBatchJobsM10
end
