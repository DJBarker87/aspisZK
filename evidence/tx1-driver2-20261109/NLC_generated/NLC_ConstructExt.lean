import NLC_FinishConstruct
import NLC_CopyFrames
set_option autoImplicit false
namespace AspisR1.NLC_ConstructExt
open AspisR1PublicPreparation
/-- A field join at ONE returned record. Field equalities are intermediate
window obligations, never permitted as unresolved row-root hypotheses. -/
theorem verified_fields {H : Type} (actual expected : r1_semantic.Verified H)
 (roots : actual.roots = expected.roots)
 (challenges : actual.challenges = expected.challenges)
 (alpha : actual.alpha = expected.alpha)
 (claims : actual.claims = expected.claims)
 (extra : actual.extra = expected.extra)
 (before : actual.before_z1 = expected.before_z1)
 (state : actual.state_before_z0 = expected.state_before_z0)
 (points : actual.z = expected.z)
 (transcript : actual.transcript = expected.transcript) : actual = expected := by
 cases actual
 cases expected
 cases roots
 cases challenges
 cases alpha
 cases claims
 cases extra
 cases before
 cases state
 cases points
 cases transcript
 rfl
#print axioms verified_fields
#print verified_fields
end AspisR1.NLC_ConstructExt
