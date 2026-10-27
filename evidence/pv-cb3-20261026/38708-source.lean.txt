import R1Z.PV_CB3_StagedIterate
import R1Z.PV_CB3_StagedHead
import R1Z.PV_CB3_StagedFinishBits
import R1Z.PV_CB3_MachineGamma
import R1Z.PV_CB3_StagedKernel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedPipelineBits
open Aeneas Aeneas.Std
open PV_CB3_StagedPacking PV_CB3_StagedIndex PV_CB3_StagedIterate

def digits (rank : Array U32 8#usize) : Array U32 8#usize :=
  ⟨(passes 8 rank).1,digits_length 8 rank⟩

def pipeline (rank : Array U32 8#usize) : Array U32 8#usize :=
  PV_CB3_StagedFinishBits.finish (digits rank) (limb (passes 8 rank).2 ⟨0,by decide⟩)

theorem bits_pipeline (rank : Array U32 8#usize) :
    bits (pipeline rank) = PV_CB3_MachineGamma.gamma (bits rank) := by
  have hs := projection 8 rank
  simp only [pipeline,PV_CB3_StagedFinishBits.bits_finish,PV_CB3_StagedHead.head_bits,
    PV_CB3_MachineGamma.gamma,PV_CB3_MachineHigh.high]
  have hd : bits (digits rank) = (PV_CB3_MachineDigits.split 8 (bits rank)).1 := hs.1
  simp only [hd,hs.2]

/-- The recursive adapter and the already checked eight-stage typed kernel
have identical array values; no arithmetic or recurrence cell is normalized. -/
theorem kernel_pipeline (rank : Array U32 8#usize) :
    PV_CB3_StagedKernel.pipeline rank = pipeline rank := by
  simp only [PV_CB3_StagedKernel.pipeline,pipeline,digits,passes,
    PV_CB3_StagedFinishBits.finish]
  rfl
#print axioms bits_pipeline
#print axioms kernel_pipeline
end R1Z.PV_CB3_StagedPipelineBits
