import NKF_BoxModel
set_option autoImplicit false
noncomputable section
namespace NKF_CheckpointBox
open Aeneas Aeneas.Std Result
abbrev C := NJQ_Carrier.CC
abbrev F := NJQ_Carrier.CF
def reference (b : Slice U8) := NKF_BoxModel.outer (NJQ_Canonical.checkpoint b)

theorem raw_child (b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (cut : NJQ_CheckpointTotal.Cut b raw) :
 ok (NKF_BoxModel.tail (NJQ_Carrier.checkpoint_result raw)) = reference b := by
 exact NKF_BoxModel.congruence _ _ (NJQ_Canonical.checkpoint_result b raw cut)

def TailCut (raw : core.result.Result C F)
 (out : core.result.Result C NKF_BoxModel.PE) : Prop :=
 out = NKF_BoxModel.tail raw

theorem source (b : Slice U8)
 (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (rawCut : NJQ_CheckpointTotal.Cut b raw)
 (out : core.result.Result C NKF_BoxModel.PE)
 (native : TailCut (NJQ_Carrier.checkpoint_result raw) out) :
 ok out = reference b := by
 rw [native]
 exact raw_child b raw rawCut
set_option pp.proofs false in
#print raw_child
#print axioms raw_child
set_option pp.proofs false in
#print source
#print axioms source
end NKF_CheckpointBox
