import NKY_BoxFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxRoots
open Aeneas Aeneas.Std Result
open NKY_BoxAction
/-- TX2:216 allocation lift. The reservation is consumed at the sole Box site,
not an unused binder. All raw/returned value clauses are discharged by the
retained CLOSED decoder and NKP complete-window reconstruction at SAME bytes.
The Allocator item interprets allocate s 176 at this invocation, not an
independent successful allocation. No allocation-success premise. -/
theorem checkpoint {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation) (owner : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE)
 (cut : NKP_BoxCuts.CheckpointCut bytes raw out) :
 run allocator before 176 reservation owner (ok out)=
 run allocator before 176 reservation owner (NKF_CheckpointBox.reference bytes) := by
 exact substitute allocator before 176 reservation owner out _
  (NKP_BoxCuts.checkpoint reservation bytes raw out cut)

/-- TX2:218, identical source order and universal allocation outcome, with the
master's native allocation request. The full Result includes allocator
fail/div, exhaustion abort, mapped decoder errors and owned success carrier. -/
theorem master {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation) (owner : Nat)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE)
 (cut : NKP_BoxCuts.MasterCut bytes raw out) :
 run allocator before 304 reservation owner (ok out)=
 run allocator before 304 reservation owner (NKF_MasterBox.reference bytes) := by
 exact substitute allocator before 304 reservation owner out _
  (NKP_BoxCuts.master reservation bytes raw out cut)
#print checkpoint
#print axioms checkpoint
#print master
#print axioms master
end AspisR1.NKY_BoxRoots
end
