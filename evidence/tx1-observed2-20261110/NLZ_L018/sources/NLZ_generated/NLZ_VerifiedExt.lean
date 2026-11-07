import NLZ_SegmentChain137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_VerifiedExt
open AspisR1PublicPreparation
/-- Compose the record-valued native windows without dropping a returned
field. This is a VALUE law only; claims' physical owner/frame stays separate. -/
theorem fields {H : Type} (a b : r1_semantic.Verified H)
 (roots : a.roots=b.roots) (challenges : a.challenges=b.challenges)
 (alpha : a.alpha=b.alpha) (claims : a.claims=b.claims)
 (extra : a.extra=b.extra) (before : a.before_z1=b.before_z1)
 (state : a.state_before_z0=b.state_before_z0) (z : a.z=b.z)
 (transcript : a.transcript=b.transcript) : a=b := by
 cases a
 cases b
 simp_all only
#print axioms fields
#print fields
end AspisR1.NLZ_VerifiedExt
end
