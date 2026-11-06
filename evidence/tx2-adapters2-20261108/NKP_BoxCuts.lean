import NKF_Roots
set_option autoImplicit false
noncomputable section
namespace NKP_BoxCuts
open Aeneas Aeneas.Std Result
/-- Reviewed native cut, NKP_K014..K041 and K044/K045, pinned by
NKP_INPUTS.json/NKP_K*_CUT.json. The assertions read the returned Box value:
`match (&raw,&out) {(Ok(a),Ok(b))=>FIELD,(Err(_),Err(e))=>
*e==ProgramError::InvalidAccountData,_=>false}`. FIELD ranges over every
scalar and bounded byte/word coordinate in NKF_Windows.Master. No allocation
identity or successful-child premise is inferred from these observations. -/
def MasterReturned (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE) : Prop :=
 match raw,out with
 | .Ok a,.Ok b => NKF_Windows.Master a b
 | .Err _,.Err e => e = .InvalidAccountData
 | _,_ => False

/-- Same assertion transcription for NKP_K002..K013 and K042/K043;
NKF_Windows.Checkpoint lists all six scalar/byte/word windows. The native
oracle returns every typed raw Result at the original immutable bytes. -/
def CheckpointReturned (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE) : Prop :=
 match raw,out with
 | .Ok a,.Ok b => NKF_Windows.Checkpoint a b
 | .Err _,.Err e => e = .InvalidAccountData
 | _,_ => False

theorem master_tail (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE)
 (cut : MasterReturned raw out) : out = NKF_BoxModel.tail raw := by
 cases raw with
 | Err e =>
   cases out with
   | Err f => exact congrArg core.result.Result.Err cut
   | Ok b => exact False.elim cut
 | Ok a =>
   cases out with
   | Err f => exact False.elim cut
   | Ok b =>
     have same := NKF_BoxFields.master a b (NKF_Windows.master_fields a b cut)
     cases same
     rfl

theorem checkpoint_tail (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE)
 (cut : CheckpointReturned raw out) : out = NKF_BoxModel.tail raw := by
 cases raw with
 | Err e =>
   cases out with
   | Err f => exact congrArg core.result.Result.Err cut
   | Ok b => exact False.elim cut
 | Ok a =>
   cases out with
   | Err f => exact False.elim cut
   | Ok b =>
     have same := NKF_BoxFields.checkpoint a b (NKF_Windows.checkpoint_fields a b cut)
     cases same
     rfl

structure MasterCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE) : Prop where
 decoder : NJQ_MasterTotal.Cut bytes raw
 returned : MasterReturned (NJQ_Carrier.master_result raw) out

structure CheckpointCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE) : Prop where
 decoder : NJQ_CheckpointTotal.Cut bytes raw
 returned : CheckpointReturned (NJQ_Carrier.checkpoint_result raw) out

/-- SAME-byte CLOSED raw153 substitution and reconstruction of every returned
field, with no successful-child, endpoint, Ops-dictionary or allocator-success
premise. Arbitrary reservation retains the existing allocator boundary. -/
theorem master (reservation : AspisR1.NP6_StdModel.Reservation)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CM NKF_BoxModel.PE)
 (cut : MasterCut bytes raw out) :
 ok out = NKF_MasterBox.reference bytes := by
 exact NKF_MasterBox.source bytes raw cut.decoder out (master_tail _ _ cut.returned)

/-- SAME-byte CLOSED raw152 substitution; all six windows and every mapped
error participate, with the same retained trust scope as master. -/
theorem checkpoint (reservation : AspisR1.NP6_StdModel.Reservation)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CC NKF_BoxModel.PE)
 (cut : CheckpointCut bytes raw out) :
 ok out = NKF_CheckpointBox.reference bytes := by
 exact NKF_CheckpointBox.source bytes raw cut.decoder out (checkpoint_tail _ _ cut.returned)

#print axioms master_tail
#print axioms checkpoint_tail
set_option pp.proofs false in
#print master
#print axioms master
set_option pp.proofs false in
#print checkpoint
#print axioms checkpoint
end NKP_BoxCuts
