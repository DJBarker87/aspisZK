from pathlib import Path
R=Path(__file__).resolve().parents[2]
q=[132355,218094,178080,149624,166165,42158,179622,21248,63860,55377,185637,14297]
for tree in range(3):
 ns=f'JGk_TX2_Positions{tree}'
 vals=[x//4 if tree==2 else x for x in q]
 raw='['+','.join(map(str,vals))+']'
 target=f'JGf_TX2_Count{2 if tree==2 else 0}.indices00'
 s=f'''import JGk_TX2_ComparatorTransport
import JGf_TX2_Count0
import JGf_TX2_Count2
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open OraclePortSelectedDraft

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries
def key := index q {tree}
def raw : List Nat := {raw}
theorem raw_keys : (batchPositions 1).map key=raw := rfl
#print axioms raw_keys
theorem distinct : ∀ a ∈ batchPositions 1, ∀ b ∈ batchPositions 1, key a=key b → a=b := by
  apply List.inj_on_of_nodup_map
  rw [raw_keys]
  decide
#print axioms distinct
theorem permutation : raw.Perm {target} := by
  apply Multiset.coe_eq_coe.mp
  simp only [raw,{target},←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero]
  ac_rfl
#print axioms permutation
theorem ordered : {target}.Pairwise (·≤·) := by decide
#print axioms ordered

theorem source : (OraclePortFrozenOrder.sortedPositions q 1 {tree}).map key={target} := by
  apply JGk_TX2_ComparatorTransport.key_stream (batchPositions 1) key _ {target}
  · intro a ha b hb
    apply decide_eq_decide.mpr
    have h := JGk_TX2_ComparatorTransport.tie_transport (batchPositions 1) key
      (fun a b => a≤b) distinct (fun _ _ => Nat.le_refl _) a ha b hb
    exact decide_eq_decide.mp h
  · rw [raw_keys]
    exact permutation
  · exact ordered
#print axioms source
end AspisR1.{ns}
end
'''
 (R/'lean'/f'{ns}.lean').write_text(s)
