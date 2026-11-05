import NGW_NewModel
import RPz7_FIn_WeightsInstall
set_option autoImplicit false
namespace NGW_NewInterface
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays
open AspisR1 AspisR1Stage2.Stage2Finish

def CanonK (x : K) : Prop := (x.c0.a.val < 2147483647 ∧ x.c0.b.val < 2147483647) ∧
 (x.c1.a.val < 2147483647 ∧ x.c1.b.val < 2147483647)

theorem alpha_domain (alpha : Array K 10#usize) (ha : Holds CanonK alpha) :
 Holds Canon (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) := by
 intro q hq
 rcases List.mem_map.mp hq with ⟨x,hx,rfl⟩
 exact ha x hx

theorem point_domain (z : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize)
 (hz : Holds (fun p=>CanonK p.x ∧ CanonK p.y) z) :
 Holds NGW_CircleInitial.CanonPoint (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) := by
 intro q hq
 rcases List.mem_map.mp hq with ⟨x,hx,rfl⟩
 exact hz x hx

theorem cohort (variant : AspisR1Stage2.transport.Variant) (alpha : Array K 10#usize)
 (z : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize)
 (ha : Holds CanonK alpha) (hz : Holds (fun p=>CanonK p.x ∧ CanonK p.y) z) :
 ∃ w,FIn_WeightsInstall.newWeights variant alpha z=ok (.Ok w) ∧
 NGW_FactorWrite.CanonFactors w.factors ∧ Holds (Holds Canon) w.points ∧ Holds Canon w.extra := by
 obtain ⟨w,run,cf,cp,ce⟩ := NGW_NewModel.source (FIn_WeightsInstall.variant variant)
   (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)
   (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) (alpha_domain alpha ha) (point_domain z hz)
 exact ⟨w,FIn_WeightsInstall.same_call variant alpha z w run,cf,cp,ce⟩

#print axioms alpha_domain
#print axioms point_domain
#print axioms cohort
end NGW_NewInterface
