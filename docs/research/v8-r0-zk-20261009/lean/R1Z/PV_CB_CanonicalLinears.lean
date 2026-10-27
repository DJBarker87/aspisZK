import R1Z.PV_CB_CanonicalLinearsLoop
import R1Z.PV_CB_CanonicalQuarticMore
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalLinears
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange
abbrev Points := PV_CB_CanonicalLinearsLoop.Points
abbrev Valid := PV_CB_CanonicalTower.Valid

theorem source (point : Points) (vp : PV_CB_CanonicalArrays.Valid Valid point) :
    ∃ linear explicitLinear,
      PV_CB_MaskSource.state_only_hiding.selected_mask_linears point = ok (linear,explicitLinear) ∧
      Valid linear ∧ Valid explicitLinear := by
  obtain ⟨suffix,weighted,hloop,vs,vw⟩ := PV_CB_CanonicalLinearsLoop.source point vp
  obtain ⟨s3,hs3,vs3⟩ := PV_CB_CanonicalQuarticMore.scale suffix 3#u32
  obtain ⟨w22,hw22,vw22⟩ := PV_CB_CanonicalQuarticMore.scale weighted 22#u32
  obtain ⟨linear,hlinear,vlinear⟩ := PV_CB_CanonicalQuartic.add s3 w22 vs3 vw22
  obtain ⟨s275,hs275,vs275⟩ := PV_CB_CanonicalQuarticMore.scale suffix 275#u32
  obtain ⟨w150,hw150,vw150⟩ := PV_CB_CanonicalQuarticMore.scale weighted 150#u32
  obtain ⟨explicitLinear,hexplicit,vexplicit⟩ := PV_CB_CanonicalQuartic.add s275 w150 vs275 vw150
  refine ⟨linear,explicitLinear,?_,vlinear,vexplicit⟩
  simp only [PV_CB_MaskLinearsFinite.S.loop,ProverRwSuccessReverseRange.before,
    PV_CB_CurrentQuartic.S.scale,PV_CB_CurrentQuartic.S.add] at hloop hs3 hw22 hlinear hs275 hw150 hexplicit
  simp only [PV_CB_MaskSource.state_only_hiding.selected_mask_linears,
    core.iter.traits.iterator.Iterator.rev.default,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
    hloop,bind_tc_ok]
  change (do
    let q ← PV_CB_CurrentQuartic.S.scale suffix 3#u32
    let q1 ← PV_CB_CurrentQuartic.S.scale weighted 22#u32
    let q2 ← PV_CB_CurrentQuartic.S.add q q1
    let q3 ← PV_CB_CurrentQuartic.S.scale suffix 275#u32
    let q4 ← PV_CB_CurrentQuartic.S.scale weighted 150#u32
    let q5 ← PV_CB_CurrentQuartic.S.add q3 q4
    ok (q2,q5)) = ok (linear,explicitLinear)
  simp only [PV_CB_CurrentQuartic.S.scale,PV_CB_CurrentQuartic.S.add,
    hs3,hw22,hlinear,hs275,hw150,hexplicit,bind_tc_ok]
#print axioms source
end R1Z.PV_CB_CanonicalLinears
