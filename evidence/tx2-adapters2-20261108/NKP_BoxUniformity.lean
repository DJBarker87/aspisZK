import NKP_BoxCuts
set_option autoImplicit false
noncomputable section
namespace NKP_BoxUniformity
open Aeneas Aeneas.Std Result
/-- The literal wrapper continuation after its sole raw-decoder call. The
byte argument occurs at that child call and nowhere in the tail. The native
source edit/erasure packet pins that fact; the typed child reply is universally
quantified, including successful replies at the representative short buffer.
Thus0..33is a harness allocation extent, not a parser/caller precondition. -/
def masterG (_bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF) := NKF_BoxModel.tail raw

def checkpointG (_bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF) := NKF_BoxModel.tail raw

theorem master_bytes_irrelevant (a b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF) :
 masterG a raw = masterG b raw := rfl

theorem checkpoint_bytes_irrelevant (a b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF) :
 checkpointG a raw = checkpointG b raw := rfl

/-- Every complete returned-field/error observation determines G at EVERY
byte slice. The native premise has no byte-length or successful-child clause.
The separate positive root then applies raw153at those SAME bytes. -/
theorem master_any_bytes (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE)
 (native : NKP_BoxCuts.MasterReturned raw out) : out = masterG bytes raw :=
 NKP_BoxCuts.master_tail raw out native

/-- Same uniformity for raw152and the checkpoint wrapper. No short-input
condition is carried into NKP_BoxCuts.checkpoint's input domain. -/
theorem checkpoint_any_bytes (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE)
 (native : NKP_BoxCuts.CheckpointReturned raw out) : out = checkpointG bytes raw :=
 NKP_BoxCuts.checkpoint_tail raw out native

#print axioms master_bytes_irrelevant
#print axioms checkpoint_bytes_irrelevant
#print axioms master_any_bytes
#print axioms checkpoint_any_bytes
end NKP_BoxUniformity
