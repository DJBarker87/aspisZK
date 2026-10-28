import NDO_JGv_QueryScalars11
import NDO_JGv_DotStep0
import NDO_JGv_DotStep1
import NDO_JGv_DotStep2
import NDO_JGv_DotStep3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotSum
open Aeneas Aeneas.Std
open scoped BigOperators
open JGv_DotData

def total : Nat → OraclePortCheckpointAbiC5.E
  | 0 => 0
  | n+1 => total n+term ⟨n%64,Nat.mod_lt _ (by omega)⟩

theorem step (n : Nat) (hn : n<64) :
    CheckpointBytes5Output.ofE (state (n+1))=CheckpointBytes5Output.ofE (state n)+term ⟨n%64,Nat.mod_lt _ (by omega)⟩ := by
  by_cases h0 : n<16
  · exact JGv_DotStep0.source n (by omega) h0
  by_cases h1 : n<32
  · exact JGv_DotStep1.source n (by omega) h1
  by_cases h2 : n<48
  · exact JGv_DotStep2.source n (by omega) h2
  exact JGv_DotStep3.source n (by omega) hn
#print axioms step

theorem source (n : Nat) (hn : n≤64) : CheckpointBytes5Output.ofE (state n)=total n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [step n (by omega),ih (by omega),total]
#print axioms source

theorem rhs : total 64=CheckpointBytes5Output.ofE JGv_QueryScalars11.rhs := by
  rw [←source 64 (by omega)]
  rfl
#print axioms rhs
theorem total_sum (n : Nat) : total n=∑ i∈Finset.range n,term ⟨i%64,Nat.mod_lt _ (by omega)⟩ := by
  induction n with
  | zero => simp only [total,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [total,Finset.sum_range_succ,ih]
#print axioms total_sum

theorem finite : (∑ i : Fin 64,term i)=total 64 := by
  rw [total_sum,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm
#print axioms finite
end AspisR1.JGv_DotSum
end
