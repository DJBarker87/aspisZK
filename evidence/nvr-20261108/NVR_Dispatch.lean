import RSL_TX1_330
-- NVR_ provenance: lines 1-21 (pure half) of evidence/entry-rsl-20261111/NNF_Dispatch.lean (research, sha256 3e0e3ec4645c4ff3...).
-- Change: split from the Aeneas transport half (now NVR_DispatchEmitted) so the RowSpec
-- folds compile against RSL rev4 without NMW/Hiq; the import NNF_Carrier is replaced by
-- its only RSL import RSL_TX1_330; namespace NNF_ -> NVR_. Definitions verbatim.
set_option autoImplicit false
noncomputable section
namespace NVR_Dispatch
open RSL
abbrev Child := TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
/-- Normal form of the emitted dispatcher on its admitted own-input domain.
All child observations are retained verbatim, including abort/divergence. -/
def process (stage1 stage2 : Child) : Child := fun a s env =>
  if TX2_221.stage1Route a.data then stage1 a s env else stage2 a s env
/-- Entry rejects before touching accounts, otherwise tail-calls process. -/
def entry (f : Child) : Child := fun a s env =>
  if TX2_221.admitted a.data then f a s env
  else ⟨.ret (.error .invalidInstructionData, s), []⟩
theorem admitted_iff (d : Bytes) : TX2_221.admitted d = true ↔
    TX2_221.stage1Route d = true ∨ d.take 4 = REQUEST_MAGIC := by
  simp only [TX2_221.admitted, TX2_221.stage1Route, Bool.or_eq_true, beq_iff_eq]

#print axioms admitted_iff
end NVR_Dispatch
end
