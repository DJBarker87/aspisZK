import NKF_Windows
set_option autoImplicit false
noncomputable section
namespace NKF_Roots
open Aeneas Aeneas.Std Result
abbrev PE := NKF_BoxModel.PE
/-- These are the parent's own reviewed native cuts. The error constructor
contains every raw error, not a successful-child premise. Success carries
scalar/window facts only; record equality is derived by extensionality. -/
inductive MasterTail : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF →
 core.result.Result NJQ_Carrier.CM PE → Prop
 | success (a b : NJQ_Carrier.CM) (fields : NKF_Windows.Master a b) :
    MasterTail (.Ok a) (.Ok b)
 | error (e : NJQ_Carrier.CF) : MasterTail (.Err e) (.Err .InvalidAccountData)

inductive CheckpointTail : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF →
 core.result.Result NJQ_Carrier.CC PE → Prop
 | success (a b : NJQ_Carrier.CC) (fields : NKF_Windows.Checkpoint a b) :
    CheckpointTail (.Ok a) (.Ok b)
 | error (e : NJQ_Carrier.CF) : CheckpointTail (.Err e) (.Err .InvalidAccountData)

theorem master_tail (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CM PE) (cut : MasterTail raw out) :
 out=NKF_BoxModel.tail raw := by
 cases cut with
 | success a b h => rw [NKF_BoxFields.master a b (NKF_Windows.master_fields a b h)];rfl
 | error e => rfl

theorem checkpoint_tail (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (out : core.result.Result NJQ_Carrier.CC PE) (cut : CheckpointTail raw out) :
 out=NKF_BoxModel.tail raw := by
 cases cut with
 | success a b h => rw [NKF_BoxFields.checkpoint a b (NKF_Windows.checkpoint_fields a b h)];rfl
 | error e => rfl

structure MasterCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CM PE) : Prop where
 decoder : NJQ_MasterTotal.Cut bytes raw
 tail : MasterTail (NJQ_Carrier.master_result raw) out

structure CheckpointCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CC PE) : Prop where
 decoder : NJQ_CheckpointTotal.Cut bytes raw
 tail : CheckpointTail (NJQ_Carrier.checkpoint_result raw) out

/-- Positive roots expose only the reviewed SAME-call native cuts. They
instantiate the CLOSED raw child at these exact bytes inside the proof.
Reservation is universally quantified; no allocator-success premise. -/
theorem master (reservation : AspisR1.NP6_StdModel.Reservation)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CM PE)
 (cut : MasterCut bytes raw out) : ok out = NKF_MasterBox.reference bytes := by
 exact NKF_MasterBox.source bytes raw cut.decoder out
  (master_tail _ _ cut.tail)

theorem checkpoint (reservation : AspisR1.NP6_StdModel.Reservation)
 (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result NJQ_Carrier.CC PE)
 (cut : CheckpointCut bytes raw out) : ok out = NKF_CheckpointBox.reference bytes := by
 exact NKF_CheckpointBox.source bytes raw cut.decoder out
  (checkpoint_tail _ _ cut.tail)
set_option pp.proofs false in
#print master_tail
#print axioms master_tail
#print axioms checkpoint_tail
set_option pp.proofs false in
#print master
#print axioms master
set_option pp.proofs false in
#print checkpoint
#print axioms checkpoint
end NKF_Roots
