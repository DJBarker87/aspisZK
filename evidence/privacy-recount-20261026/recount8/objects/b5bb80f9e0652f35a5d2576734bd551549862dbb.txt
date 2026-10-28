import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressLiftSelectors
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower

def initial (tag : U32) : Q := ⟨⟨tag,0#u32⟩,⟨0#u32,0#u32⟩⟩

variable [ExternalTypes]

theorem complex (ops : ExternalFuns) (tag : U32) :
    (PV_CurrentScaleInstall.selected ops).op61 tag = ok (⟨tag,0#u32⟩ : C) := by
  change mapResult fromC (AspisR1ProducerRelease47.field.CM31.from_m31 tag) = _
  simp only [AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.M31.ZERO,mapResult,fromC]

theorem quartic (ops : ExternalFuns) (c : C) :
    (PV_CurrentScaleInstall.selected ops).op66 c = ok (⟨c,⟨0#u32,0#u32⟩⟩ : Q) := by
  change mapResult fromQ (AspisR1ProducerRelease47.field.QM31.from_cm31 (toC c)) = _
  simp only [AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.CM31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO,
    mapResult,fromQ,fromC,toC]

theorem initial_state (ops : ExternalFuns) (tag : U32) :
    (do
      let c ← (PV_CurrentScaleInstall.selected ops).op61 tag
      (PV_CurrentScaleInstall.selected ops).op66 c) = ok (initial tag) := by
  rw [complex]
  simp only [bind_tc_ok,quartic]
  rfl
#print axioms complex
#print axioms quartic
#print axioms initial_state
end R1Z.PV_RW_CompressLiftSelectors
