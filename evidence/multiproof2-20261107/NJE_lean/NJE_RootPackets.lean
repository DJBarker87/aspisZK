import NJA_Context

set_option autoImplicit false
noncomputable section
namespace NJE_RootPackets
open Aeneas Aeneas.Std Result NJA_Multiproof
attribute [local instance] Classical.propDecidable

theorem TX1_124 {α : Type} (s : MultiproofConeRef.reference.Scratch)
    (root : Array U8 32#usize) (k : Bool → Result α) :
    multiproof.root_matches s.val root = ok (decide (s.val.val[0]! = root)) ∧
    (do let b ← multiproof.root_matches s.val root; k b) =
      k (decide (s.val.val[0]! = root)) :=
  ⟨NJA_Root.cohort_comparison s root, NJA_Context.root s root k⟩

theorem TX2_090 {α : Type} (s : MultiproofConeRef.reference.Scratch)
    (root : Array U8 32#usize) (k : Bool → Result α) :
    multiproof.root_matches s.val root = ok (decide (s.val.val[0]! = root)) ∧
    (do let b ← multiproof.root_matches s.val root; k b) =
      k (decide (s.val.val[0]! = root)) := TX1_124 s root k

#print TX1_124
#print axioms TX1_124
#print TX2_090
#print axioms TX2_090
end NJE_RootPackets
end
