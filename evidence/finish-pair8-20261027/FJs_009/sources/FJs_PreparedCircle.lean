import FJs_PreparedPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_PreparedCircle
open Aeneas Aeneas.Std Result
abbrev K := OraclePortCheckpointAbiC5.K
abbrev P := FJr_PairRows.P
attribute [local irreducible] QuadraticAlgebra.instInv

theorem coordinates (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) (p0 p1 : P)
    (h0 : Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 0#usize=ok p0)
    (h1 : Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 1#usize=ok p1) :
    FJc_WeightValues.decode p0.x=pm.coordinates 0 ∧
    FJc_WeightValues.decode p0.y=pm.coordinates 1 ∧
    FJc_WeightValues.decode p1.x=pm.coordinates 2 ∧
    FJc_WeightValues.decode p1.y=pm.coordinates 3 := by
  have size := p.z.property
  change p.z.val.length=2 at size
  have slots0 := FJc_ReadSlot.slot _ _ _ h0
  have slots1 := FJc_ReadSlot.slot _ _ _ h1
  change (p.z.val.map FIn_WeightsInstall.toPoint)[0]?=some p0 at slots0
  change (p.z.val.map FIn_WeightsInstall.toPoint)[1]?=some p1 at slots1
  have coords := fields.coordinates
  obtain ⟨z0,z1,zs⟩ := List.length_eq_two.mp size
  simp only [zs,List.map_cons,List.map_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.some.injEq] at slots0 slots1
  subst p0;subst p1
  simp only [zs,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
    List.ofFn_succ,List.ofFn_zero,List.map_cons,List.map_nil,List.cons.injEq] at coords
  obtain ⟨x0,y0,x1,y1,_⟩ := coords
  change FJc_WeightValues.decode (FIn_WeightsInstall.toQ z0.x)=_ ∧
    FJc_WeightValues.decode (FIn_WeightsInstall.toQ z0.y)=_ ∧
    FJc_WeightValues.decode (FIn_WeightsInstall.toQ z1.x)=_ ∧
    FJc_WeightValues.decode (FIn_WeightsInstall.toQ z1.y)=_
  rw [x0,y0,x1,y1]
  exact ⟨FJs_PreparedPoint.decode _,FJs_PreparedPoint.decode _,FJs_PreparedPoint.decode _,FJs_PreparedPoint.decode _⟩

#print axioms coordinates
end AspisR1.FJs_PreparedCircle
end
