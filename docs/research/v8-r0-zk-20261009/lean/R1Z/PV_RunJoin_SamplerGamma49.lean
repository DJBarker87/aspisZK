import R1Z.PV_RunJoin_SamplerRaw49
import R1Z.PV_RunJoin_SamplerFields49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerGamma49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) :
    ∃ a : Raw,@sampler.gamma_sample (types base) (selected base heap box ops) block=
      ok (ProverRwDictionaryTower.fromW (source a)) ∧ canonical a := by
  obtain ⟨digits,he,hc,hv,hp,hb⟩ := @PV_B2_E_GammaOriginal.gamma_law (types base) ops block
  have hc' := PV_B2_C_GammaSource.canonical_array digits hc
  refine ⟨PV_RunJoin_SamplerRaw49.raw digits,?_,PV_RunJoin_SamplerRaw49.canonical digits hc'⟩
  change @ExternalFuns.op249 (types base) (selected base heap box ops) block=_
  rw [PV_RunJoin_SamplerFields49.gamma base heap box ops]
  have eq : PV_B2_E_GammaOriginal.callback block=
      ok (PV_B2_E_OrdinaryOriginal.toNative (PV_B2_C_ArrayDigits.raw digits)) := he
  exact eq.trans (congrArg Result.ok (PV_RunJoin_SamplerRaw49.native digits))
#print axioms complete
end R1Z.PV_RunJoin_SamplerGamma49
