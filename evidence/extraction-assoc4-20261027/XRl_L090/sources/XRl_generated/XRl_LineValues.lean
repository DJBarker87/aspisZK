import XRl_GeometryStep
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools
namespace XRl_LineValues
/-- Exact five-lane append and line-z computation at one actual successful
source iteration. This is a source-call projection, not finite-field algebra
or the native allocation/source-to-ELF association. -/
theorem continuation (start : Usize) (it next : core.slice.iter.Iter U32) (query : U32)
    (lines flat outLines outFlat : alloc.vec.Vec aspis_core.field.M31)
    (hnext : core.slice.iter.IteratorSliceIter.next it=ok (some query,next))
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok (.cont (next,outLines,outFlat))) :
    ∃ (fibre : aspis_core.r0.domain.FibreIndex) (point : aspis_core.r0.domain.Point aspis_core.field.M31)
      (xIndex yIndex : aspis_core.r0.domain.FibreIndex)
      (x y square double one z : aspis_core.field.M31),
      fast_domain.fibre_point fibre=ok point ∧ fast_domain.line_node xIndex=ok x ∧
      fast_domain.line_node yIndex=ok y ∧ aspis_core.field.M31.mul x x=ok square ∧
      aspis_core.field.M31.double square=ok double ∧ aspis_core.field.M31.ONE=ok one ∧
      aspis_core.field.M31.sub double one=ok z ∧
      outLines.val=lines.val++[z] ∧ outFlat.val=flat.val++[point.x,point.y,x,y,z] := by
  unfold verifier.QueryGeometry.for_range_loop0.body at run
  rw [hnext,bind_tc_ok] at run
  obtain ⟨u,_,run⟩ := bind_success _ _ _ run
  obtain ⟨ru,_,run⟩ := bind_success _ _ _ run
  obtain ⟨r,_,run⟩ := bind_success _ _ _ run
  cases r with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at run
    cases run
  | Ok fibre =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨point,hpoint,run⟩ := bind_success _ _ _ run
    obtain ⟨group,_,run⟩ := bind_success _ _ _ run
    obtain ⟨first,_,run⟩ := bind_success _ _ _ run
    obtain ⟨rx,_,run⟩ := bind_success _ _ _ run
    obtain ⟨r,_,run⟩ := bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok fibreX =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨lineX,hx,run⟩ := bind_success _ _ _ run
      obtain ⟨again,_,run⟩ := bind_success _ _ _ run
      obtain ⟨last,_,run⟩ := bind_success _ _ _ run
      obtain ⟨ry,_,run⟩ := bind_success _ _ _ run
      obtain ⟨r,_,run⟩ := bind_success _ _ _ run
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        cases run
      | Ok fibreY =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        obtain ⟨lineY,hy,run⟩ := bind_success _ _ _ run
        obtain ⟨square,hsquare,run⟩ := bind_success _ _ _ run
        obtain ⟨double,hdouble,run⟩ := bind_success _ _ _ run
        obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
        obtain ⟨lineZ,hz,run⟩ := bind_success _ _ _ run
        try simp only [lift,bind_tc_ok] at run
        obtain ⟨iter,_,run⟩ := bind_success _ _ _ run
        obtain ⟨zero,ignored,_,run⟩ := pair_bind_success _ _ _ run
        split at run
        · have same := Result.ok.inj run
          subst out
          cases run
        · obtain ⟨flat1,hflat,run⟩ := bind_success _ _ _ run
          obtain ⟨lines1,hlines,run⟩ := bind_success _ _ _ run
          have same := ControlFlow.cont.inj (Result.ok.inj run)
          have hlinesEq := congrArg (fun s : XRk_GeometryStep.State => s.2.1) same
          have hflatEq := congrArg (fun s : XRk_GeometryStep.State => s.2.2) same
          change lines1=outLines at hlinesEq
          change flat1=outFlat at hflatEq
          subst lines1
          subst flat1
          refine ⟨fibre,point,fibreX,fibreY,lineX,lineY,square,double,one,lineZ,
            hpoint,hx,hy,hsquare,hdouble,hone,hz,?_,?_⟩
          · have h := hlines
            unfold alloc.vec.Vec.push at h
            dsimp only at h
            split at h
            · have eq := congrArg (fun v : alloc.vec.Vec aspis_core.field.M31 => v.val) (Result.ok.inj h)
              simpa only [List.concat_eq_append] using eq.symm
            · cases h
          · exact XRl_GeometryVectors.extend flat outFlat _ hflat
#print axioms continuation
end XRl_LineValues
