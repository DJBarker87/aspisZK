import NNG_Nonempty094
import RSL_TX1_328
set_option autoImplicit false
namespace AspisR1.NNG_PropagatedFinding328
open RSL

/-- Interface finding only: the mapper's allocation/log cannot repair an
empty observation relation at its preceding094 call. No328 candidate is attempted. -/
theorem required_width (a : TX1_328.Args LIB_Instances.VL) (env : Env)
 (o : Obs (Except ProgramError Bytes)) (k : a.k=10)
 (law : TX1_328.Ref LIB_Instances.VL LIB_Instances.P a env o) : a.proof.length=57607 := by
 exact NNG_DomainFinding094.bind_inherits _ _ _ env o
  (fun before called=>NNG_DomainFinding094.required_width a env before k called.2) law
#print axioms required_width

theorem no_candidate : ¬∃ impl,TX1_328.RowSpec_328 LIB_Instances.VL LIB_Instances.P impl := by
 rintro ⟨impl,candidate⟩
 let a : TX1_328.Args LIB_Instances.VL:=⟨NNG_Nonempty094.public_,[],[],10⟩
 have law:=candidate a env0 NNG_Nonempty094.public_domain
 have width:=required_width a env0 (impl a env0) rfl law
 change 0=57607 at width
 cases width
#print axioms no_candidate
end AspisR1.NNG_PropagatedFinding328
