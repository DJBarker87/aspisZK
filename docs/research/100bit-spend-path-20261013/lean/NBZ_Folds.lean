import NBZ_Wide
set_option autoImplicit false
noncomputable section
namespace NBZ_Folds
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NBO_TailDomain (WideCanonical)
/-- Frozen inverse-scaled circle coefficient schedule. The four scales are
provided by the exact M31 product calls, not chosen fold outputs. -/
def circle (alpha a b c d : Stage2E) (quarter qiy qix qixiy : U32) : Result Stage2E := do
 let h0 ← NBW_Coefficients.coefficient a b c d true true true quarter
 let h1 ← NBW_Coefficients.coefficient a b c d false false true qiy
 let h2 ← NBW_Coefficients.coefficient a b c d true false false qix
 let h3 ← NBW_Coefficients.coefficient a b c d false true false qixiy
 NBW_Horner.eval NBZ_Wide.product alpha [h0,h1,h2] h3
/-- Concrete domain discharge for every coefficient and each of the three
Horner products. No successful fold return is supplied as a hypothesis. -/
theorem circle_total (alpha a b c d : Stage2E) (quarter qiy qix qixiy : U32)
 (halpha : WideCanonical alpha) (ha : WideCanonical a) (hb : WideCanonical b)
 (hc : WideCanonical c) (hd : WideCanonical d) :
 ∃ out, circle alpha a b c d quarter qiy qix qixiy=ok out ∧ WideCanonical out := by
 obtain ⟨h0,e0,c0⟩ := NBW_Coefficients.coefficient_total a b c d true true true quarter ha hb hc hd
 obtain ⟨h1,e1,c1⟩ := NBW_Coefficients.coefficient_total a b c d false false true qiy ha hb hc hd
 obtain ⟨h2,e2,c2⟩ := NBW_Coefficients.coefficient_total a b c d true false false qix ha hb hc hd
 obtain ⟨h3,e3,c3⟩ := NBW_Coefficients.coefficient_total a b c d false true false qixiy ha hb hc hd
 obtain ⟨out,run,canonical⟩ := NBZ_Wide.horner_total alpha h3 halpha c3 [h0,h1,h2]
   (by intro h mem; simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
       rcases mem with rfl | rfl | rfl <;> assumption)
 exact ⟨out,by simp only [circle,e0,e1,e2,e3,bind_tc_ok,run],canonical⟩
/-- Frozen line fold, including c0/c1 construction and their subsequent use.
Each scale is the corresponding native scalar-call return. -/
def line (alpha a b c d : Stage2E) (quarter qiz hix hiy half hiz : U32) : Result Stage2E := do
 let h0 ← NBW_Coefficients.coefficient a b c d true true true quarter
 let h2 ← NBW_Coefficients.coefficient a b c d true false false qiz
 let ab ← NBO_FoldLinear.sub a b
 let c0 ← NBO_FoldLinear.scale ab hix
 let dc ← NBO_FoldLinear.sub d c
 let c1 ← NBO_FoldLinear.scale dc hiy
 let sum ← NBO_FieldSemantics.add c0 c1
 let h1 ← NBO_FoldLinear.scale sum half
 let diff ← NBO_FoldLinear.sub c0 c1
 let h3 ← NBO_FoldLinear.scale diff hiz
 NBW_Horner.eval NBZ_Wide.product alpha [h0,h1,h2] h3
/-- Domains of c0/c1 are consequences of their SAME earlier returns. -/
theorem line_total (alpha a b c d : Stage2E) (quarter qiz hix hiy half hiz : U32)
 (halpha : WideCanonical alpha) (ha : WideCanonical a) (hb : WideCanonical b)
 (hc : WideCanonical c) (hd : WideCanonical d) :
 ∃ out, line alpha a b c d quarter qiz hix hiy half hiz=ok out ∧ WideCanonical out := by
 obtain ⟨h0,e0,c0⟩ := NBW_Coefficients.coefficient_total a b c d true true true quarter ha hb hc hd
 obtain ⟨h2,e2,c2⟩ := NBW_Coefficients.coefficient_total a b c d true false false qiz ha hb hc hd
 obtain ⟨ab,eab,cab⟩ := NBO_FoldLinear.sub_total a b ha hb
 obtain ⟨u,eu,cu⟩ := NBO_FoldLinear.scale_total ab hix
 obtain ⟨dc,edc,cdc⟩ := NBO_FoldLinear.sub_total d c hd hc
 obtain ⟨v,ev,cv⟩ := NBO_FoldLinear.scale_total dc hiy
 obtain ⟨sum,esum,csum⟩ := NBO_FieldSemantics.add_total u v cu cv
 obtain ⟨h1,e1,c1⟩ := NBO_FoldLinear.scale_total sum half
 obtain ⟨diff,ediff,cdiff⟩ := NBO_FoldLinear.sub_total u v cu cv
 obtain ⟨h3,e3,c3⟩ := NBO_FoldLinear.scale_total diff hiz
 obtain ⟨out,run,canonical⟩ := NBZ_Wide.horner_total alpha h3 halpha c3 [h0,h1,h2]
   (by intro h mem; simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
       rcases mem with rfl | rfl | rfl <;> assumption)
 exact ⟨out,by simp only [line,e0,e2,eab,eu,edc,ev,esum,e1,ediff,e3,bind_tc_ok,run],canonical⟩
#print axioms circle_total
#print axioms line_total
end NBZ_Folds
end
