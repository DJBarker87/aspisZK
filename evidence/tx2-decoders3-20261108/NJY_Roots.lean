import NJY_Identity
import NJY_Checkpoint
import NJY_Master
import NJY_Entry
import NJY_Registry
import NJQ_Canonical
set_option autoImplicit false
noncomputable section
namespace NJY_Roots
open Aeneas Aeneas.Std Result
/-- All five references target complete Results. Cut parameters below are the
reviewed source-ordered native transcriptions; no child-success, endpoint,
arbitrary operation dictionary or runtime Boolean is a separate premise. -/
theorem identity (b : Slice U8) :
 NJY_Identity.reference b=NJY_Identity.model b := NJY_Identity.source b

theorem checkpoint (b : Slice U8)
 (out : core.result.Result NJQ_Checkpoint.C NJQ_Checkpoint.F)
 (cut : NJY_Checkpoint.Cut b out) : ok out=NJY_Checkpoint.model b := by
 rw [← NJQ_Checkpoint.source]
 exact NJY_Checkpoint.source b out cut

theorem master (b : Slice U8)
 (out : core.result.Result NJQ_Master.M NJQ_Master.F)
 (cut : NJY_Master.Cut b out) : ok out=NJY_Master.model b := by
 rw [← NJQ_Master.source]
 exact NJY_Master.source b out cut

theorem entry (b : Slice U8) (log : Option NJI_V1Carrier.E)
 (out : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F)
 (cut : NJY_Entry.Cut b log out) : ok out=NJY_Entry.model b := by
 rw [← NJQ_Entry.source]
 exact NJY_Entry.source b log out cut

theorem registry (b : Slice U8) (log : Option NJI_V1Carrier.R)
 (out : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F)
 (cut : NJY_Registry.Cut b log out) : ok out=NJY_Registry.model b := by
 rw [← NJQ_Registry.source]
 exact NJY_Registry.source b log out cut

set_option pp.proofs false in
#print identity
#print axioms identity
set_option pp.proofs false in
#print checkpoint
#print axioms checkpoint
set_option pp.proofs false in
#print master
#print axioms master
set_option pp.proofs false in
#print entry
#print axioms entry
set_option pp.proofs false in
#print registry
#print axioms registry
end NJY_Roots
