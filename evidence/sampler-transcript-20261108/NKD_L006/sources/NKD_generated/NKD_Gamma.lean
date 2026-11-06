import NKD_Low
import NKD_Add
import NKD_Decode
import NGT_Reduction
set_option autoImplicit false
namespace AspisR1.NKD_Gamma
open Aeneas Aeneas.Std Result NGT_NBL_SamplerReplay
/-- Both branch cuts retain native low/add/packing observations on one invocation. -/
abbrev Cut (block : Bytes32) (out : AspisR1PublicPreparation.aspis_core.field.WideExact) :=
 NGT_Reduction.Scalar block true out
/-- TX1:158: the actual installed cohort sampler, without a free callee dictionary. -/
theorem root (block : Bytes32) (out : AspisR1PublicPreparation.aspis_core.field.WideExact)
 (cut : Cut block out) : NGT_NBA_Installed.actual.sampling.gamma block = ok out :=
 NGT_Reduction.scalar cut
#print root
#print axioms root
end AspisR1.NKD_Gamma
