import R1Z.PV_OptB_CopySelection
import R0Z.BuilderModelCopyKinds
import R1Z.PoleMassR1
set_option autoImplicit false
namespace R1Z.PV_OptB_PathRegistry
open R0P
open R0Z.BuilderModel (pathBase pathBase_lt)

def rightLink (level : Fin 24) : CopyLink :=
  copyLinksAfterPositivity.get ⟨48+3*level.val,by
    have length : copyLinksAfterPositivity.length = 118 := rfl
    rw [length]
    have := level.isLt
    omega⟩

theorem member (level : Fin 24) : rightLink level ∈ copyLinks := by
  have found : rightLink level ∈ copyLinksAfterPositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inr found)

/-- Only 24 selected table records are normalized, never a field trace. -/
theorem descriptor (level : Fin 24) :
    (rightLink level).tag = 1124073538+3*level.val ∧
    (rightLink level).producer.row = ⟨pathBase level+1,pathBase_lt level⟩ ∧
    (rightLink level).producer.slot = 1 ∧
    (rightLink level).producer.pattern = 13 := by
  fin_cases level <;> decide

theorem active (level : Fin 24) : CopyActiveRow (rightLink level).producer.row := by
  fin_cases level <;> decide

theorem pattern13 {K : Type} [Field K] (o : Fin 16 → K) :
    copyPatternTuple (copyPatterns 13) o =
      fun i => if h : i.val < 8 then o ⟨8+i.val,by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple,copyPatterns,copyPattern13]

theorem value_mem {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (A : Trace K) (lam : K) (level : Fin 24) :
    copyTupleValue lam (copyProducerTuple A (rightLink level)) ∈
      PoleMassR1.poleSet A lam := by
  have selected := PV_OptB_CopySelection.producer_value A lam (rightLink level) (member level)
  have belongs := PoleMassR1.poleValue_mem A lam
    ((rightLink level).producer.row,(rightLink level).producer.slot,true) (active level)
  change copyRowValues A lam (rightLink level).producer.row CopyLink.producer
    (rightLink level).producer.slot ∈ PoleMassR1.poleSet A lam at belongs
  rw [selected] at belongs
  exact belongs

#print axioms member
#print axioms descriptor
#print axioms active
#print axioms pattern13
#print axioms value_mem
end R1Z.PV_OptB_PathRegistry
