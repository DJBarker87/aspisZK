import NCI_PendingReducer
import OraclePortCkptAbiTry
set_option autoImplicit false
namespace AspisR1.NCI_PendingValue
open Aeneas Aeneas.Std Result
open S8Kani2MutableExtraction

def Canonical (q : aspis_core.field.QM31) : Prop :=
  q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧ q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647

theorem successful_value (self : batched_weights.BatchedWeights) (index : Usize)
    (q : aspis_core.field.QM31) (success : batched_weights.BatchedWeights.value self index=ok q) :
    Canonical q := by
  unfold batched_weights.BatchedWeights.value at success
  obtain ⟨lane,_,h⟩ := AspisR1.OraclePortCkptAbiTry.bind_success _ _ _ success
  obtain ⟨x0,_,h⟩ := AspisR1.OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨m0,r0,_,c0⟩ := NCI_PendingReducer.reducer_ok x0
  rw [r0,bind_tc_ok] at h
  obtain ⟨x1,_,h⟩ := AspisR1.OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨m1,r1,_,c1⟩ := NCI_PendingReducer.reducer_ok x1
  rw [r1,bind_tc_ok] at h
  obtain ⟨x2,_,h⟩ := AspisR1.OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨m2,r2,_,c2⟩ := NCI_PendingReducer.reducer_ok x2
  rw [r2,bind_tc_ok] at h
  obtain ⟨x3,_,h⟩ := AspisR1.OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨m3,r3,_,c3⟩ := NCI_PendingReducer.reducer_ok x3
  rw [r3,bind_tc_ok] at h
  simp [Array.index_usize,Array.make] at h
  subst q
  exact ⟨c0,c1,c2,c3⟩
#print axioms successful_value
end AspisR1.NCI_PendingValue
