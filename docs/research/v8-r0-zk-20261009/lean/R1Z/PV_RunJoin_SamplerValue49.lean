import R1Z.PV_RunJoin_SamplerOrdinary49
import R1Z.PV_RunJoin_SamplerGamma49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerValue49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (nonzero : Bool) :
    ∃ a : Raw,(if nonzero then @sampler.gamma_sample (types base) (selected base heap box ops) block
      else @sampler.ordinary_sample (types base) (selected base heap box ops) block)=
      ok (ProverRwDictionaryTower.fromW (source a)) ∧ canonical a := by
  cases nonzero with
  | false => exact PV_RunJoin_SamplerOrdinary49.complete base heap box ops block
  | true => exact PV_RunJoin_SamplerGamma49.complete base heap box ops block

def value (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (nonzero : Bool) : Raw :=
  Classical.choose (complete base heap box ops block nonzero)

theorem spec (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (nonzero : Bool) :
    (if nonzero then @sampler.gamma_sample (types base) (selected base heap box ops) block
      else @sampler.ordinary_sample (types base) (selected base heap box ops) block)=
      ok (ProverRwDictionaryTower.fromW (source (value base heap box ops block nonzero))) ∧
    canonical (value base heap box ops block nonzero) :=
  Classical.choose_spec (complete base heap box ops block nonzero)
#print axioms complete
#print axioms value
#print axioms spec
end R1Z.PV_RunJoin_SamplerValue49
