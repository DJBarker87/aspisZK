import RowFinish_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_RoundUnique
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open RowFinish_Control
variable {W : Type}

/-- Source determinism identifies the entire record, including its dependent
 uses as the next round's claim. No canonicality or arithmetic law is needed. -/
theorem unique (ops : FinishOps W) (bytes : Slice U8) (alpha claim : E)
    (x y : RoundValues ops bytes alpha claim) : x = y := by
  rcases x with ⟨x0,x4,xl,xq,xr,xv,hx0,hx4,hxl,hxq,hxr,hxv⟩
  rcases y with ⟨y0,y4,yl,yq,yr,yv,hy0,hy4,hyl,hyq,hyr,hyv⟩
  have e0 : x0 = y0 := Result.ok.inj (hx0.symm.trans hy0)
  have e4 : x4 = y4 := Result.ok.inj (hx4.symm.trans hy4)
  subst y0; subst y4
  have el : xl = yl := Result.ok.inj (hxl.symm.trans hyl)
  have eq : xq = yq := Result.ok.inj (hxq.symm.trans hyq)
  subst yl; subst yq
  have er : xr = yr := Result.ok.inj (hxr.symm.trans hyr)
  have ev : xv = yv := Result.ok.inj (hxv.symm.trans hyv)
  subst yr; subst yv
  rfl

#print axioms unique
end AspisR1.SAF_RoundUnique
end
