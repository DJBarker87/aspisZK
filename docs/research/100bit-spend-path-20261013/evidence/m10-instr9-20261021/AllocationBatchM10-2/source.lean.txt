import RecoveryParserAllocationM10
import SharedFiniteMaterializationM10
import BinEagerRecoveryWork

set_option autoImplicit false
namespace AspisR1.AllocationBatchM10

def cells {n : Nat} (heap : Fin n → Nat) : Nat := (List.ofFn heap).sum+3*n+1

theorem sum_le {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  simpa only [List.ofFn_eq_map] using
    RecoveryParserAllocationM10.sum_mono (List.finRange n) f g (fun i _ => h i)

theorem materialize_work {A : Type} {n : Nat} (f : Fin n → A × Nat)
    (heap : Fin n → Nat) (h : ∀ i, heap i ≤ (f i).2) :
    cells heap ≤ (BinTypedWordDemandWork.materialize f).2 := by
  have hs := sum_le heap (fun i => (f i).2) h
  simpa only [cells,BinTypedWordDemandWork.materialize,List.map_ofFn,Function.comp_def] using Nat.add_le_add_right (Nat.add_le_add_right hs (3*n)) 1

theorem batch_work {A : Type} {n : Nat} (f : Fin n → A × Nat)
    (heap : Fin n → Nat) (h : ∀ i, heap i ≤ (f i).2) :
    cells heap ≤ (SharedFiniteMaterializationM10.batch f).2 := materialize_work f heap h

theorem recovery_work {n : Nat} (f : Fin n → BinEagerRecoveryWork.Leaf × Nat)
    (heap : Fin n → Nat) (h : ∀ i, heap i ≤ (f i).2) :
    cells heap ≤ (BinEagerRecoveryWork.materialize f).2 := by
  have hs := sum_le heap (fun i => (f i).2) h
  simpa only [cells,BinEagerRecoveryWork.materialize,BinEagerWordsReads.materialize,
    List.map_ofFn,Function.comp_def] using Nat.add_le_add_right (Nat.add_le_add_right hs (3*n)) 1

#print axioms sum_le
#print axioms materialize_work
#print axioms batch_work
#print axioms recovery_work
end AspisR1.AllocationBatchM10
