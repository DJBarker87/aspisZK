import XRm_ResultCuts
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools XRm_ResultCuts
namespace XRm_QueryIndices
theorem reached (start : Usize) (it next : core.slice.iter.Iter U32) (query : U32)
    (lines flat outLines outFlat : alloc.vec.Vec aspis_core.field.M31)
    (hnext : core.slice.iter.IteratorSliceIter.next it=ok (some query,next))
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok (.cont (next,outLines,outFlat))) :
    ∃ (point : aspis_core.r0.domain.Point aspis_core.field.M31) (group first last : Usize)
      (x y : aspis_core.field.M31),
      (UScalar.cast .Usize query)<262144#usize ∧
      fast_domain.fibre_point (UScalar.cast .Usize query)=ok point ∧
      (UScalar.cast .Usize query)/4#usize=ok group ∧
      group*4#usize=ok first ∧ first+3#usize=ok last ∧
      fast_domain.line_node first=ok x ∧ fast_domain.line_node last=ok y := by
  unfold verifier.QueryGeometry.for_range_loop0.body at run
  rw [hnext,bind_tc_ok] at run
  obtain ⟨u,hu,run⟩ := bind_success _ _ _ run
  obtain ⟨ru,hru,run⟩ := bind_success _ _ _ run
  obtain ⟨r,hmap,run⟩ := bind_success _ _ _ run
  cases r with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at run
    cases run
  | Ok fibre =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨point,hpoint,run⟩ := bind_success _ _ _ run
    obtain ⟨group,hgroup,run⟩ := bind_success _ _ _ run
    obtain ⟨first,hfirst,run⟩ := bind_success _ _ _ run
    obtain ⟨rx,hrx,run⟩ := bind_success _ _ _ run
    obtain ⟨r,hmapX,run⟩ := bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok fibreX =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨lineX,hx,run⟩ := bind_success _ _ _ run
      obtain ⟨again,hagain,run⟩ := bind_success _ _ _ run
      obtain ⟨last,hlast,run⟩ := bind_success _ _ _ run
      obtain ⟨ry,hry,run⟩ := bind_success _ _ _ run
      obtain ⟨r,hmapY,run⟩ := bind_success _ _ _ run
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        cases run
      | Ok fibreY =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        obtain ⟨lineY,hy,run⟩ := bind_success _ _ _ run
        have ru_ok := map_err_ok _ ru () fibre hmap
        rw [ru_ok] at hru
        have fi := XRm_ResultCuts.fibre u fibre hru
        have rx_ok := map_err_ok _ rx () fibreX hmapX
        rw [rx_ok] at hrx
        have fx := XRm_ResultCuts.fibre first fibreX hrx
        have ry_ok := map_err_ok _ ry () fibreY hmapY
        rw [ry_ok] at hry
        have fy := XRm_ResultCuts.fibre last fibreY hry
        have castEq : UScalar.cast .Usize query=u := Result.ok.inj hu
        have firstEq := Result.ok.inj (hfirst.symm.trans hagain)
        refine ⟨point,group,first,last,lineX,lineY,?_,?_,?_,hfirst,?_,?_,?_⟩
        · simpa only [castEq] using fi.2
        · simpa only [fi.1,castEq] using hpoint
        · simpa only [castEq] using hgroup
        · simpa only [←firstEq] using hlast
        · simpa only [fx.1] using hx
        · simpa only [fy.1] using hy
#print axioms reached
end XRm_QueryIndices
