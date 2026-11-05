import NGW_FactorOuter
import NGW_CircleOuter
import NGW_PointsPacket
set_option autoImplicit false
namespace NGW_NewModel
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem source (variant : FIn_WeightsExtract.FInVariant) (alpha : Array Q 10#usize)
 (z : Array NGW_CircleInitial.Point 2#usize) (ha : Holds Canon alpha)
 (hz : Holds NGW_CircleInitial.CanonPoint z) :
 ∃ w,FIn_WeightsExtract.weights_new variant alpha z=ok (.Ok w) ∧
 CanonFactors w.factors ∧ Holds (Holds Canon) w.points ∧ Holds Canon w.extra := by
 obtain ⟨points,_,_,pointRun,pointCanon⟩ := NGW_PointsPacket.cohort alpha ha
 let a8 := NGM_GuardExact.pick alpha 8 (by decide)
 let a9 := NGM_GuardExact.pick alpha 9 (by decide)
 have read8 := NGM_GuardExact.index alpha 8#usize (by decide)
 have read9 := NGM_GuardExact.index alpha 9#usize (by decide)
 have ca8 := canonical_pick Canon alpha 8 (by decide) ha
 have ca9 := canonical_pick Canon alpha 9 (by decide) ha
 let initial := Array.repeat 5#usize (Array.repeat 5#usize (Array.repeat 4#usize FIn_WeightsExtract.field.QM31.ZERO))
 have ci : CanonFactors initial := repeated CanonPlane 5#usize _
   (repeated CanonRow 5#usize _ (repeated Canon 4#usize _ zero))
 obtain ⟨regular,regularRun,regularCanon⟩ := NGW_FactorOuter.source points initial 0#usize (by decide) pointCanon ci
 obtain ⟨factors,circleRun,circleCanon⟩ := NGW_CircleOuter.source z regular 0#usize (by decide) hz regularCanon
 let extra := Array.make 2#usize [a8,a9]
 let w : FIn_WeightsExtract.Weights := ⟨variant,factors,points,extra⟩
 refine ⟨w,?_,circleCanon,pointCanon,?_⟩
 · simp only [FIn_WeightsExtract.weights_new,pointRun,read8,read9,regularRun,circleRun,
     FIn_WeightsExtract.Weights.box_from_parts,bind_tc_ok]
   rfl
 · intro q hq
   simp only [extra,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl
   · exact ca8
   · exact ca9

#print axioms source
end NGW_NewModel
