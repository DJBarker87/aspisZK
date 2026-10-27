import RPu_FIw_CopyMeaning
import R0P.Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CopyTransport
open FIv_NativeValue (K decode)
open FIv_NativeArray (value)
open FIw_CopyMeaning

def row (r : Row) : R0P.CopyRowExtension K where
  producerValues := fun i=>value r.producer_values i.val
  producerWeights := fun i=>value r.producer_weights i.val
  consumerValues := fun i=>value r.consumer_values i.val
  consumerWeights := fun i=>value r.consumer_weights i.val

/-- Exact transport of the residual arithmetic. This does not yet identify
its row with the model's 136-link fold. -/
theorem value_exact (r : Row) (helper chi : K) :
    residual r helper chi=R0P.copyResidual (row r) helper chi := by
  rfl
#print axioms value_exact
end AspisR1.FIw_CopyTransport
end
