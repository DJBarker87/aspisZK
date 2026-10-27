import R1Z.PV_CB3_StagedResult
import R1Z.PV_CB3_StagedWords
import R1Z.PV_CB3_Op249Staged
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedGammaRank
open Aeneas Aeneas.Std Result ProverRwFull

def result (block : Array U8 32#usize) : aspis_core.field.wide_exact.WideExact :=
  PV_CB3_StagedUnpack.raw (PV_CB3_StagedKernel.pipeline (PV_CB3_StagedWords.words block))

def byteRank (block : Array U8 32#usize) : Nat :=
  PV_CB3_SamplerCarry.value 256 (block.val.map UScalar.val)

def outputRank (x : aspis_core.field.wide_exact.WideExact) : Nat :=
  PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base (PV_CB3_StagedUnpack.values x)

/-- Entire extracted owned reference, with no desired-output or canonicality premise. -/
theorem source (block : Array U8 32#usize) :
    PV_CB3_StagedSource.staged_reference.gamma block = ok (result block) := by
  rw [PV_CB3_StagedResult.source,PV_CB3_StagedWords.source]
  rfl

theorem rank (block : Array U8 32#usize) :
    outputRank (result block) = byteRank block % (PV_CB3_SamplerWord.base^8-1)+1 := by
  unfold outputRank result byteRank
  rw [PV_CB3_StagedResult.value,PV_CB3_StagedWords.value]

/-- Prospective selected callback law; native shipped/reference P6 is still open. -/
theorem selected [ExternalTypes] (ops : ExternalFuns) (block : Array U8 32#usize) :
    (PV_CB3_Op249Staged.selected ops).op249 block = ok (result block) := source block
#print axioms source
#print axioms rank
#print axioms selected
end R1Z.PV_CB3_StagedGammaRank
