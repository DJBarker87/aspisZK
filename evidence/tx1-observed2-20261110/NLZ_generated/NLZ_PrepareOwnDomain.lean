import NLZ_Split087
import NLR_PrepareArgumentDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_PrepareOwnDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Exact ORIGINAL compact-y1 bytes consumed by179. -/
def compact (i : NLJ_Prepare.Input Unit) : Slice U8 := NGV_ByteWindow.select i.proof 7031 464
/-- Proposed087 OWN-argument domain under(bf), not a success or endpoint
hypothesis. Its canonicality clause must be discharged by094's strict scan;
no087 row root is submitted. -/
structure Domain (i : NLJ_Prepare.Input Unit) : Prop where
 proofLength : i.proof.val.length=57607
 compactCanonical : NFU_Retarget.compact.check_values (compact i)=ok (.Ok ())
theorem compact_width (i : NLJ_Prepare.Input Unit) (size : i.proof.val.length=57607) :
 (compact i).val.length=464 := by
 change ((i.proof.val.drop 7031).take 464).length=464
 rw [List.length_take,List.length_drop,size]
 omega
#print axioms compact_width
#print Domain
end AspisR1.NLZ_PrepareOwnDomain
end
