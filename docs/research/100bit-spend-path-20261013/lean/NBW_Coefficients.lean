import NBW_Horner
set_option autoImplicit false
noncomputable section
namespace NBW_Coefficients
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NBO_TailDomain (WideCanonical)
def linear4 (a b c d : Stage2E) (ab bc cd : Bool) : Result Stage2E := do
 let x ← if ab then NBO_FieldSemantics.add a b else NBO_FoldLinear.sub a b
 let y ← if bc then NBO_FieldSemantics.add x c else NBO_FoldLinear.sub x c
 if cd then NBO_FieldSemantics.add y d else NBO_FoldLinear.sub y d
private theorem binary (a b : Stage2E) (plus : Bool)
 (ha : WideCanonical a) (hb : WideCanonical b) :
 ∃ z, (if plus then NBO_FieldSemantics.add a b else NBO_FoldLinear.sub a b)=ok z ∧
 WideCanonical z := by
 cases plus
 · exact NBO_FoldLinear.sub_total a b ha hb
 · exact NBO_FieldSemantics.add_total a b ha hb
/-- All four native coefficient sign patterns are covered on the exact
canonical inputs; intermediate canonicality is derived, never assumed. -/
theorem linear4_total (a b c d : Stage2E) (ab bc cd : Bool)
 (ha : WideCanonical a) (hb : WideCanonical b)
 (hc : WideCanonical c) (hd : WideCanonical d) :
 ∃ z, linear4 a b c d ab bc cd=ok z ∧ WideCanonical z := by
 obtain ⟨x,hx,cx⟩ := binary a b ab ha hb
 obtain ⟨y,hy,cy⟩ := binary x c bc cx hc
 obtain ⟨z,hz,cz⟩ := binary y d cd cy hd
 exact ⟨z,by simp only [linear4,hx,hy,bind_tc_ok,hz],cz⟩
def coefficient (a b c d : Stage2E) (ab bc cd : Bool) (scale : U32) : Result Stage2E := do
 let sum ← linear4 a b c d ab bc cd
 NBO_FoldLinear.scale sum scale
/-- The retained scalar theorem handles all U32 scales. A canonical scale
is still required by the native scalar stub and must be checked there. -/
theorem coefficient_total (a b c d : Stage2E) (ab bc cd : Bool) (scale : U32)
 (ha : WideCanonical a) (hb : WideCanonical b)
 (hc : WideCanonical c) (hd : WideCanonical d) :
 ∃ z, coefficient a b c d ab bc cd scale=ok z ∧ WideCanonical z := by
 obtain ⟨sum,hs,cs⟩ := linear4_total a b c d ab bc cd ha hb hc hd
 obtain ⟨z,hz,cz⟩ := NBO_FoldLinear.scale_total sum scale
 exact ⟨z,by simp only [coefficient,hs,bind_tc_ok,hz],cz⟩
#print axioms binary
#print axioms linear4_total
#print axioms coefficient_total
end NBW_Coefficients
end
