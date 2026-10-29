import R1Z.PhaseWireLog2Bin

/-! The source splits its ordered q22 array before per-batch sorting. A set of
queries cannot recover that split. These small witnesses do not enumerate Fib.
No claim about reachability under a concrete cryptographic hash is made. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SerJoinOrderObstruction

abbrev Query := Fin 262144

def first : List Query :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]

def crossed : List Query :=
  [0,1,2,3,4,5,6,7,8,9,11,10,12,13,14,15,16,17,18,19,20,21]

-- Reduction is bounded by two 22-element lists, never Finset.univ.
theorem witnesses_valid :
    first.length = 22 ∧ first.Nodup ∧ crossed.length = 22 ∧ crossed.Nodup := by
  decide

theorem same_query_set : first.toFinset = crossed.toFinset := by decide

theorem different_first_batch :
    (first.take 11).toFinset ≠ (crossed.take 11).toFinset := by decide

/-- Even the unordered contents of batch A fail to factor through the q22 set.
Sorting each source batch cannot repair loss of the boundary. -/
theorem no_set_batch_factorization (batch : Finset Query → Finset Query) :
    ¬ (∀ qs : List Query, qs.length = 22 → qs.Nodup →
      batch qs.toFinset = (qs.take 11).toFinset) := by
  intro h
  have ha := h first witnesses_valid.1 witnesses_valid.2.1
  have hb := h crossed witnesses_valid.2.2.1 witnesses_valid.2.2.2
  rw [same_query_set] at ha
  exact different_first_batch (ha.symm.trans hb)

/-- This obstruction uses the actual D111 batchQueries definition, with all
other challenge fields fixed. At least one valid ordering fails the split. -/
theorem cannot_match_both (ch : R0Z.JointView.Challenges PrivacyR1AcctBasis.K) :
    ¬ (PhaseWireLog2Bin.batchQueries {ch with queries := first.toFinset} 0 =
        (first.take 11).toFinset ∧
       PhaseWireLog2Bin.batchQueries {ch with queries := crossed.toFinset} 0 =
        (crossed.take 11).toFinset) := by
  rintro ⟨ha, hb⟩
  rw [same_query_set] at ha
  exact different_first_batch (ha.symm.trans hb)

#print axioms witnesses_valid
#print axioms same_query_set
#print axioms different_first_batch
#print axioms no_set_batch_factorization
#print axioms cannot_match_both
end R1Z.SerJoinOrderObstruction
