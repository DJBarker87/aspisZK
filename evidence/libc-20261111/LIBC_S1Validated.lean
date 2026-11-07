import LIBC_S1Sources
import LIB_VPublicDomain
set_option autoImplicit false
noncomputable section
namespace LIBC_S1Validated
open Aeneas Aeneas.Std AspisR1
/-- Independent emitted-copy routes give the SAME semantic Public, down to
every retained payment, transition, digest and frontier coordinate. -/
theorem public_copy (p : NMT_345.Public) :
 FIq_Carriers.toPublic (NMT_345Prep.toT5 p)=NMT_345FIq.toT5 p := by
 cases p <;> rfl
/-- CLOSED276 at the SAME statement supplies LIB_'s actual hd-only publicDom
for CLOSED268. The SAME validator
returned-true arm is the implication antecedent; no free domain is assumed. -/
theorem validated (s : NMT_345.Statement) (good : LIBC_S1.valid s=true) :
 LIB_VPublicDomain.publicDigestDom (NMT_345Prep.toT5 (NMT_345.semanticValue s)) := by
 have h := NMT_345.validated_public_domain s ((LIBC_S1.valid_iff s).mp good)
 unfold LIB_VPublicDomain.publicDigestDom
 rw [public_copy]
 exact h
#print axioms public_copy
#print axioms validated
end LIBC_S1Validated
