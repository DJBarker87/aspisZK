import R1Z.PV_OptB_PathRegistry
import R1Z.PV_OptB_WitnessFamily
set_option autoImplicit false
namespace R1Z.PV_OptB_PathTuple
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R0Z.BuilderModel
open PV_OptB_PathRegistry
variable {K : Type} [Field K] [DecidableEq K]

theorem right_cell (pub : Public K) (w : Witness K) (level : Fin 24)
    (direction : (w.path level).1 = false) (j : Fin 8) :
    buildModel pub (modelWitness w) ⟨8+j.val,by omega⟩ ⟨pathBase level+1,pathBase_lt level⟩ =
      (w.path level).2 j := by
  rw [buildModel,cell_aux _ _ (by show 8+j.val < 16; omega) _
    (by show 57 ≤ (pathBase level+1)/16; unfold pathBase; omega),
    pathSucc_aux,pathSuccCell_right _ _ j rfl]
  change (ordered (treeCur (modelWitness w) (inputLeaf pub (modelWitness w)) level.val)
    (w.path level).2 (w.path level).1).2 j = (w.path level).2 j
  rw [direction]
  rfl

theorem tuple_shape (pub : Public K) (w : Witness K) (level : Fin 24)
    (direction : (w.path level).1 = false) :
    copyProducerTuple (buildModel pub (modelWitness w)) (rightLink level) =
      (((1124073538+3*level.val : Nat) : K),fun i : Fin 16 =>
        if h : i.val < 8 then (w.path level).2 ⟨i.val,h⟩ else 0) := by
  rw [copyProducerTuple,copyEndpointTuple,(descriptor level).1,
    (descriptor level).2.1,(descriptor level).2.2.2,pattern13]
  congr 1
  funext i
  split_ifs with hi
  · exact right_cell pub w level direction ⟨i.val,hi⟩
  · rfl

#print axioms right_cell
#print axioms tuple_shape
end R1Z.PV_OptB_PathTuple
