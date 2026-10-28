import NDO_JGk_TX2_ScratchIndices
import Port4B_CountInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_CountSource
open Aeneas Aeneas.Std Result
def front0 (s : MultiproofConeRef.reference.Scratch) : Slice U32 :=
  ⟨(JGk_TX2_Scratch0.s12 s).idx.val.take 12,by
    have bound := List.length_take_le 12 (JGk_TX2_Scratch0.s12 s).idx.val
    scalar_tac⟩
theorem raw0 (s : MultiproofConeRef.reference.Scratch) :
    (front0 s).val.map UScalar.val=JGf_TX2_Count0.indices00 := by
  change ((JGk_TX2_Scratch0.s12 s).idx.val.take 12).map UScalar.val=_
  rw [JGk_TX2_ScratchIndices.front0_12]
  rfl
#print axioms raw0
theorem well0 (s : MultiproofConeRef.reference.Scratch) :
    OraclePortFrozenOrder.wellFormed ((front0 s).val.map UScalar.val) := by
  rw [raw0]
  refine ⟨by decide,by decide,by decide,?_⟩
  intro i hi
  simp only [JGf_TX2_Count0.indices00,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
#print axioms well0
theorem source0 (s : MultiproofConeRef.reference.Scratch) :
    Port4B_Install.leaves.op11 .Two (front0 s)=ok (some 163#usize) := by
  change Port4B_CountInstall.nodeCount .Two (front0 s)=_
  unfold Port4B_CountInstall.nodeCount
  rw [dif_pos (well0 s)]
  have value : Port4B_CountInstall.countValue ((front0 s).val.map UScalar.val) (well0 s)=163#usize := by
    apply UScalar.eq_of_val_eq
    change MultiproofConeCountLevels.sourceCount 18 ((front0 s).val.map UScalar.val)=163
    rw [raw0,JGf_TX2_Count0.total00]
  rw [value]
#print axioms source0
def front1 (s : MultiproofConeRef.reference.Scratch) : Slice U32 :=
  ⟨(JGk_TX2_Scratch1.s12 s).idx.val.take 12,by
    have bound := List.length_take_le 12 (JGk_TX2_Scratch1.s12 s).idx.val
    scalar_tac⟩
theorem raw1 (s : MultiproofConeRef.reference.Scratch) :
    (front1 s).val.map UScalar.val=JGf_TX2_Count0.indices00 := by
  change ((JGk_TX2_Scratch1.s12 s).idx.val.take 12).map UScalar.val=_
  rw [JGk_TX2_ScratchIndices.front1_12]
  rfl
#print axioms raw1
theorem well1 (s : MultiproofConeRef.reference.Scratch) :
    OraclePortFrozenOrder.wellFormed ((front1 s).val.map UScalar.val) := by
  rw [raw1]
  refine ⟨by decide,by decide,by decide,?_⟩
  intro i hi
  simp only [JGf_TX2_Count0.indices00,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
#print axioms well1
theorem source1 (s : MultiproofConeRef.reference.Scratch) :
    Port4B_Install.leaves.op11 .Two (front1 s)=ok (some 163#usize) := by
  change Port4B_CountInstall.nodeCount .Two (front1 s)=_
  unfold Port4B_CountInstall.nodeCount
  rw [dif_pos (well1 s)]
  have value : Port4B_CountInstall.countValue ((front1 s).val.map UScalar.val) (well1 s)=163#usize := by
    apply UScalar.eq_of_val_eq
    change MultiproofConeCountLevels.sourceCount 18 ((front1 s).val.map UScalar.val)=163
    rw [raw1,JGf_TX2_Count0.total00]
  rw [value]
#print axioms source1
def front2 (s : MultiproofConeRef.reference.Scratch) : Slice U32 :=
  ⟨(JGk_TX2_Scratch2.s12 s).idx.val.take 12,by
    have bound := List.length_take_le 12 (JGk_TX2_Scratch2.s12 s).idx.val
    scalar_tac⟩
theorem raw2 (s : MultiproofConeRef.reference.Scratch) :
    (front2 s).val.map UScalar.val=JGf_TX2_Count2.indices00 := by
  change ((JGk_TX2_Scratch2.s12 s).idx.val.take 12).map UScalar.val=_
  rw [JGk_TX2_ScratchIndices.front2_12]
  rfl
#print axioms raw2
theorem well2 (s : MultiproofConeRef.reference.Scratch) :
    OraclePortFrozenOrder.wellFormed ((front2 s).val.map UScalar.val) := by
  rw [raw2]
  refine ⟨by decide,by decide,by decide,?_⟩
  intro i hi
  simp only [JGf_TX2_Count2.indices00,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
#print axioms well2
theorem source2 (s : MultiproofConeRef.reference.Scratch) :
    Port4B_Install.leaves.op11 .Two (front2 s)=ok (some 141#usize) := by
  change Port4B_CountInstall.nodeCount .Two (front2 s)=_
  unfold Port4B_CountInstall.nodeCount
  rw [dif_pos (well2 s)]
  have value : Port4B_CountInstall.countValue ((front2 s).val.map UScalar.val) (well2 s)=141#usize := by
    apply UScalar.eq_of_val_eq
    change MultiproofConeCountLevels.sourceCount 18 ((front2 s).val.map UScalar.val)=141
    rw [raw2,JGf_TX2_Count2.total00]
  rw [value]
#print axioms source2
end AspisR1.JGk_TX2_CountSource
end
