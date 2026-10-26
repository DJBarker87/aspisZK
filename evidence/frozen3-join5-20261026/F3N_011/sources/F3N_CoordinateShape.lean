import F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_CoordinateShape
open Aeneas Aeneas.Std AspisR1PublicPreparation
attribute [local irreducible] F3L_RhoMeaning.decode

theorem coordinates (out : verifier.Prepared) (p0 p1 : aspis_core.circle.SecureCirclePoint)
    (points : out.z=Array.make 2#usize [p0,p1]) :
    (F3L_SourcePrepared.numeric out).coordinates=(fun j : Fin 4=>
      if j.val=0 then F3L_RhoMeaning.decode p0.x
      else if j.val=1 then F3L_RhoMeaning.decode p0.y
      else if j.val=2 then F3L_RhoMeaning.decode p1.x
      else F3L_RhoMeaning.decode p1.y) := by
  funext j
  change F3L_RhoMeaning.decode (F3L_SourcePrepared.coordinate out j)=_
  have p0eq : F3L_SourcePrepared.point out 0=p0 :=
    congrArg (fun z : Array aspis_core.circle.SecureCirclePoint 2#usize=>
      z.val[0] '(by have h : z.val.length=2:=z.property;omega)) points
  have p1eq : F3L_SourcePrepared.point out 1=p1 :=
    congrArg (fun z : Array aspis_core.circle.SecureCirclePoint 2#usize=>
      z.val[1] '(by have h : z.val.length=2:=z.property;omega)) points
  fin_cases j <;> simp only [F3L_SourcePrepared.coordinate,p0eq,p1eq] <;> rfl

#print axioms coordinates
end AspisR1.F3N_CoordinateShape
end
