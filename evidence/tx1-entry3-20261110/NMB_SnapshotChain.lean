import NMB_SnapshotPacket
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotChain
open Aeneas Aeneas.Std Result AspisR1 S2Trust
/-- Original SDK-world step, separate from the algebraic metadata value view.
All three uses below share the SAME heap and the preceding returned world. -/
def Step {W : Type} (x : NMB_Input.Input) (L : Library W (Nat → NMB_Input.Owned))
 (before after : W) (a : Nat) : Prop :=
 ∃ token owner w1 w2,
 L.run before (.shared a token owner)=(w1,.guard token) ∧
 L.run w1 (.deref token)=(w2,.payload ((NMB_Heap.heap x).payload ((NMB_Heap.heap x).accounts a).1)) ∧
 L.run w2 (.drop token)=(after,.unit) ∧ L.related after (NMB_Heap.heap x)
theorem three {W : Type} (x : NMB_Input.Input)
 (L : Library W (Nat → NMB_Input.Owned)) (sdk : S2TrustedSdkBorrow L)
 (w : W) (related : L.related w (NMB_Heap.heap x)) (valid : Valid (NMB_Heap.heap x)) :
 ∃ w1 w2 w3,Step x L w w1 0 ∧ Step x L w1 w2 1 ∧ Step x L w2 w3 2 := by
 obtain ⟨t0,o0,a0,b0,w1,h01,h02,h03,h04⟩ := NMB_SnapshotPacket.bracket x L sdk w related valid 0
 obtain ⟨t1,o1,a1,b1,w2,h11,h12,h13,h14⟩ := NMB_SnapshotPacket.bracket x L sdk w1 h04 valid 1
 obtain ⟨t2,o2,a2,b2,w3,h21,h22,h23,h24⟩ := NMB_SnapshotPacket.bracket x L sdk w2 h14 valid 2
 exact ⟨w1,w2,w3,⟨t0,o0,a0,b0,h01,h02,h03,h04⟩,
   ⟨t1,o1,a1,b1,h11,h12,h13,h14⟩,⟨t2,o2,a2,b2,h21,h22,h23,h24⟩⟩
#print Step
#print three
#print axioms three
end NMB_SnapshotChain
