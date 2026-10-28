import NCD_B_NBS_GeometryDomains
import NBS_GeometryInstall
set_option autoImplicit false
noncomputable section
namespace NCD_GeometryCutDomains
open Aeneas Aeneas.Std Result AspisR1
/-- SAME checked query proves the actual aligned line constructor domains.
No independent successful FibreIndex result is supplied. -/
theorem aligned {Err : Type} (error : Err) (query fibre : Usize)
    (run : NBS_FibreIndex.checked error query=ok (.Ok fibre)) :
    fibre=query ∧ fibre.val<262144 ∧
      fibre.val/4*4<262144 ∧ fibre.val/4*4+3<262144 := by
  obtain ⟨same,domain⟩ := NBS_FibreIndex.accepted error query fibre run
  obtain ⟨left,right,_,_⟩ := NBS_GeometryDomains.aligned fibre.val domain
  exact ⟨same,domain,left,right⟩
/-- Reuse the canonical source primitive instance at the caller's exact
installed dictionary. This is a lower-callee domain law, not a native row result. -/
theorem primitives {Err : Type} (error : Err) (seed : NBS_GeometryInstall.Ops Err) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (NBS_GeometryInstall.primitives error seed) :=
  NBS_GeometryInstall.canonical error seed
#print axioms aligned
#print axioms primitives
end NCD_GeometryCutDomains
end
