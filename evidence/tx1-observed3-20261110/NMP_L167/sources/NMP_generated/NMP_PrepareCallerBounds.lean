import NMP_CanonicalPackets
set_option autoImplicit false
namespace AspisR1.NMP_PrepareCallerBounds
open RSL
/-- These two constructor/expansion widths follow from canonical087's OWN
input domain, with no canonicality, successful child or allocator premise. -/
theorem compressed (V : VLib) (a : TX1_087.Args V) (obs : Observer)
 (domain : TX1_087.Domain V a obs) :
 (slice a.proof OFF_SEMANTIC OFF_Y1).length=7015 ∧
 (slice a.proof OFF_Y1 OFF_INACTIVE).length=464 := by
 have size : a.proof.length=57607 := domain.1
 simp only [slice,OFF_SEMANTIC,OFF_Y1,OFF_INACTIVE,List.length_take,List.length_drop]
 rw [size]
 omega
/-- Apply after the CLOSED filled law supplies the SAME returned bytes/length;
this is a derived child-output property, never an added parent hypothesis. -/
theorem split (logical : Bytes) (size : logical.length=LOGICAL_SEMANTIC+LOGICAL_Y1) :
 (logical.take LOGICAL_SEMANTIC).length=13831 ∧
 (logical.drop LOGICAL_SEMANTIC).length=928 := by
 simp only [LOGICAL_SEMANTIC,LOGICAL_Y1] at size ⊢
 simp only [List.length_take,List.length_drop]
 omega
#print axioms compressed
#print axioms split
end AspisR1.NMP_PrepareCallerBounds
