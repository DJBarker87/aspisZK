import JGk_TX2_ComparatorTransport
import NDO_JGf_TX2_Count0
import NDO_JGf_TX2_Count2
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_Positions2
open OraclePortSelectedDraft

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries
def key := index q 2
def raw : List Nat := [33088,54523,44520,37406,41541,10539,44905,5312,15965,13844,46409,3574]
theorem raw_keys : (batchPositions 1).map key=raw := rfl
#print axioms raw_keys
theorem distinct : ∀ a ∈ batchPositions 1, ∀ b ∈ batchPositions 1, key a=key b → a=b := by
  apply List.inj_on_of_nodup_map
  rw [raw_keys]
  decide
#print axioms distinct
theorem permutation : raw.Perm JGf_TX2_Count2.indices00 := by
  apply Multiset.coe_eq_coe.mp
  simp only [raw,JGf_TX2_Count2.indices00,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero]
  ac_rfl
#print axioms permutation
theorem ordered : JGf_TX2_Count2.indices00.Pairwise (·≤·) := by decide
#print axioms ordered

theorem source : (OraclePortFrozenOrder.sortedPositions q 1 2).map key=JGf_TX2_Count2.indices00 := by
  apply JGk_TX2_ComparatorTransport.key_stream (batchPositions 1) key _ JGf_TX2_Count2.indices00
  · intro a ha b hb
    apply decide_eq_decide.mpr
    have h := JGk_TX2_ComparatorTransport.tie_transport (batchPositions 1) key
      (fun a b => a≤b) distinct (fun _ _ => Nat.le_refl _) a ha b hb
    exact decide_eq_decide.mp h
  · rw [raw_keys]
    exact permutation
  · exact ordered
#print axioms source
end AspisR1.JGk_TX2_Positions2
end
