import RPz7_FIo_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_PartNames
open Aeneas Aeneas.Std
/-- Source order in weights.rs::Weights::raw and the seven-entry parts array.
These names identify source programs; they do not assert their model meaning. -/
inductive Part where
  | inactive | point | successor | absorption | libra | circle0 | circle1
  deriving DecidableEq

def index : Part → Usize
  | .inactive => 0#usize | .point => 1#usize | .successor => 2#usize
  | .absorption => 3#usize | .libra => 4#usize | .circle0 => 5#usize
  | .circle1 => 6#usize

def source (w : FIo_Install.W) (p : Part) (j : Usize) :=
  FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) (index p) j

theorem inactive_source (w : FIo_Install.W) (j : Usize) :
    source w .inactive j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 0#usize j := rfl
theorem point_source (w : FIo_Install.W) (j : Usize) :
    source w .point j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 1#usize j := rfl
theorem successor_source (w : FIo_Install.W) (j : Usize) :
    source w .successor j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 2#usize j := rfl
theorem absorption_source (w : FIo_Install.W) (j : Usize) :
    source w .absorption j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 3#usize j := rfl
theorem libra_source (w : FIo_Install.W) (j : Usize) :
    source w .libra j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 4#usize j := rfl
theorem circle0_source (w : FIo_Install.W) (j : Usize) :
    source w .circle0 j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 5#usize j := rfl
theorem circle1_source (w : FIo_Install.W) (j : Usize) :
    source w .circle1 j=FIo_Native.weights.Weights.raw (FIo_Install.toWeights w) 6#usize j := rfl
#print axioms inactive_source
#print axioms point_source
#print axioms successor_source
#print axioms absorption_source
#print axioms libra_source
#print axioms circle0_source
#print axioms circle1_source
end AspisR1.FJc_PartNames
end
