import NNU_MerkleNative
import NKV_ConcreteDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleCount
open Aeneas Aeneas.Std Result OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

theorem source (indices : Slice U32) :
 NKV_ConcreteChildren.count .Two indices=Port4B_CountInstall.nodeCount .Two indices := by
 obtain ⟨out,run,value⟩ := NKV_ConcreteDomains.count indices
 rw [run]
 unfold Port4B_CountInstall.nodeCount
 split
 next well =>
   simp only [if_pos well] at value
   cases out with
   | none => cases value
   | some x =>
     have v : x.val=nodeCount 18 (indices.val.map UScalar.val) := Option.some.inj value
     have counted : (Port4B_CountInstall.countValue _ well).val=nodeCount 18 (indices.val.map UScalar.val) :=
       MultiproofConeCountLevels.count_eq _ _ well.2.2.1
     have same : x=Port4B_CountInstall.countValue _ well := UScalar.eq_of_val_eq (v.trans counted.symm)
     rw [same]
 next bad =>
   simp only [if_neg bad] at value
   cases out with
   | none => rfl
   | some x => cases value
#print axioms source
end AspisR1.NNU_MerkleCount
end
