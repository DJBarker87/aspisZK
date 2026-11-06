import NJY_Identity
import NJQ_MasterTotal
set_option autoImplicit false
noncomputable section
namespace NJY_Master
open Aeneas Aeneas.Std Result
/-- NJY-RT153: NJQ's complete reference and finite step/frame induction. -/
abbrev reference := NJQ_Master.reference
abbrev model := NJQ_Master.model
abbrev Cut := NJQ_MasterTotal.Cut
/-- Identity149, policy150 and validator157 are instantiated at the SAME
windows/record inside the imported composition. No successful child premise. -/
theorem source (b : Slice U8)
 (out : core.result.Result NJQ_Master.M NJQ_Master.F) (cut : Cut b out) :
 ok out = reference b := NJQ_MasterTotal.native_source b out cut
set_option pp.proofs false in
#print source
#print axioms source
end NJY_Master
