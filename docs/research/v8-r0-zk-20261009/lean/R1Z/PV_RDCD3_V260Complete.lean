import R1Z.PV_RDCD3_V260Callback
import R1Z.PV_RDCD3_Control194
import R1Z.PV_RDCD3_WordAll194
import R1Z.PV_RDCD3_Index194
import R1Z.PV_RDCD3_Range194
import R1Z.PV_RDCD3_V260Bounds

namespace R1Z.PV_RDCD3_V260Complete
set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-- Both retained operation APIs, with all inputs universally quantified and
complete Result behavior. No dictionary, inverse assumption or success-domain
hypothesis is added. Source/primitive trust qualifications are in the receipts. -/
theorem complete :
    (∀ (w : PV_B2_253c1.host_weights.Weights) (kind j : Usize),
      PV_B2_253c1.host_weights.Weights.raw w kind j =
        PV_RDCD3_V260Exact.original w kind j) ∧
    (∀ (w : PV_B2_251c1.host_weights.Weights) (kind j : Usize),
      PV_B2_251c1.host_weights.raw_value w kind j =
        PV_RDCD3_V260C_Exact.original w kind j) :=
  ⟨PV_RDCD3_V260.source,PV_RDCD3_V260Callback.source⟩

#print axioms complete
#print axioms PV_RDCD3_V260.source
#print axioms PV_RDCD3_V260.carrier
#print axioms PV_RDCD3_V260.invalid_D
#print axioms PV_RDCD3_V260Callback.source
#print axioms PV_RDCD3_V260Callback.carrier
end R1Z.PV_RDCD3_V260Complete
