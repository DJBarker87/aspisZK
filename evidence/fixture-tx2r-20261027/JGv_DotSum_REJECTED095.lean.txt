import JGv_QueryScalars11
import JGv_DotProducts0
import JGv_DotProducts1
import JGv_DotProducts2
import JGv_DotProducts3
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
  interval_cases n
  · exact JGv_DotProducts0.step00
  · exact JGv_DotProducts0.step01
  · exact JGv_DotProducts0.step02
  · exact JGv_DotProducts0.step03
  · exact JGv_DotProducts0.step04
  · exact JGv_DotProducts0.step05
  · exact JGv_DotProducts0.step06
  · exact JGv_DotProducts0.step07
  · exact JGv_DotProducts0.step08
  · exact JGv_DotProducts0.step09
  · exact JGv_DotProducts0.step10
  · exact JGv_DotProducts0.step11
  · exact JGv_DotProducts0.step12
  · exact JGv_DotProducts0.step13
  · exact JGv_DotProducts0.step14
  · exact JGv_DotProducts0.step15
  · exact JGv_DotProducts1.step16
  · exact JGv_DotProducts1.step17
  · exact JGv_DotProducts1.step18
  · exact JGv_DotProducts1.step19
  · exact JGv_DotProducts1.step20
  · exact JGv_DotProducts1.step21
  · exact JGv_DotProducts1.step22
  · exact JGv_DotProducts1.step23
  · exact JGv_DotProducts1.step24
  · exact JGv_DotProducts1.step25
  · exact JGv_DotProducts1.step26
  · exact JGv_DotProducts1.step27
  · exact JGv_DotProducts1.step28
  · exact JGv_DotProducts1.step29
  · exact JGv_DotProducts1.step30
  · exact JGv_DotProducts1.step31
  · exact JGv_DotProducts2.step32
  · exact JGv_DotProducts2.step33
  · exact JGv_DotProducts2.step34
  · exact JGv_DotProducts2.step35
  · exact JGv_DotProducts2.step36
  · exact JGv_DotProducts2.step37
  · exact JGv_DotProducts2.step38
  · exact JGv_DotProducts2.step39
  · exact JGv_DotProducts2.step40
  · exact JGv_DotProducts2.step41
  · exact JGv_DotProducts2.step42
  · exact JGv_DotProducts2.step43
  · exact JGv_DotProducts2.step44
  · exact JGv_DotProducts2.step45
  · exact JGv_DotProducts2.step46
  · exact JGv_DotProducts2.step47
  · exact JGv_DotProducts3.step48
  · exact JGv_DotProducts3.step49
  · exact JGv_DotProducts3.step50
  · exact JGv_DotProducts3.step51
  · exact JGv_DotProducts3.step52
  · exact JGv_DotProducts3.step53
  · exact JGv_DotProducts3.step54
  · exact JGv_DotProducts3.step55
  · exact JGv_DotProducts3.step56
  · exact JGv_DotProducts3.step57
  · exact JGv_DotProducts3.step58
  · exact JGv_DotProducts3.step59
  · exact JGv_DotProducts3.step60
  · exact JGv_DotProducts3.step61
  · exact JGv_DotProducts3.step62
  · exact JGv_DotProducts3.step63
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
