import NJQ_CheckpointTotal
import NJQ_Canonical
set_option autoImplicit false
noncomputable section
namespace NJY_Checkpoint
open Aeneas Aeneas.Std Result
/-- NJY-RT152: NJQ's complete reviewed reference, including the ordered
reserved scan, CLOSED digest146 Result and rejecting-prefix loop induction. -/
abbrev reference := NJQ_Checkpoint.reference
abbrev model := NJQ_Checkpoint.model
abbrev Cut := NJQ_CheckpointTotal.Cut
/-- Every slice: all native segment observations constitute the reviewed cut;
no extra digest-success or loop-success hypothesis is accepted. -/
theorem source (b : Slice U8)
 (out : core.result.Result NJQ_Checkpoint.C NJQ_Checkpoint.F) (cut : Cut b out) :
 ok out = reference b := NJQ_CheckpointTotal.native_source b out cut
set_option pp.proofs false in
#print source
#print axioms source
end NJY_Checkpoint
