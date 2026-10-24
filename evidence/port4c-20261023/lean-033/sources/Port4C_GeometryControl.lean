import Port4C_GeometryGather

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryControl
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)
variable {CoreError : Type}
abbrev M := aspis_core.field.M31

/-- An active source gather step cannot return a successful geometry. -/
theorem active_not_done (ops : Ops CoreError) (start : Usize)
    (iter iter1 : core.slice.iter.Iter U32) (query : U32)
    (zs flat : alloc.vec.Vec M) (out : verifier.QueryGeometry)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1)) :
    verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat ≠ ok (done (.Ok out)) := by
  intro h
  unfold verifier.QueryGeometry.for_range_loop0.body at h
  rw [next,bind_tc_ok] at h
  obtain ⟨u,hu,h⟩ := bind_success _ _ _ h
  obtain ⟨domain,hdom,h⟩ := bind_success _ _ _ h
  cases domain with
  | Err e => cases h
  | Ok fibre =>
    simp only [Aeneas.Std.uncurry,Port4C_GeometryStd.install,Port4C_GeometryStd.mapError,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨point,hpoint,h⟩ := bind_success _ _ _ h
    obtain ⟨parent,hparent,h⟩ := bind_success _ _ _ h
    obtain ⟨left,hleft,h⟩ := bind_success _ _ _ h
    obtain ⟨domainLeft,hdomLeft,h⟩ := bind_success _ _ _ h
    cases domainLeft with
    | Err e => cases h
    | Ok fleft =>
      simp only [Aeneas.Std.uncurry,Port4C_GeometryStd.mapError,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨lineX,hlineX,h⟩ := bind_success _ _ _ h
      obtain ⟨left1,hleft1,h⟩ := bind_success _ _ _ h
      obtain ⟨right,hright,h⟩ := bind_success _ _ _ h
      obtain ⟨domainRight,hdomRight,h⟩ := bind_success _ _ _ h
      cases domainRight with
      | Err e => cases h
      | Ok fright =>
        simp only [Aeneas.Std.uncurry,Port4C_GeometryStd.mapError,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        obtain ⟨lineY,hlineY,h⟩ := bind_success _ _ _ h
        obtain ⟨square,hsquare,h⟩ := bind_success _ _ _ h
        obtain ⟨doubled,hdoubled,h⟩ := bind_success _ _ _ h
        obtain ⟨one,hone,h⟩ := bind_success _ _ _ h
        obtain ⟨lineZ,hlineZ,h⟩ := bind_success _ _ _ h
        obtain ⟨s,hs,h⟩ := bind_success _ _ _ h
        obtain ⟨it,hit,h⟩ := bind_success _ _ _ h
        obtain ⟨⟨bad,after⟩,hzero,h⟩ := bind_success _ _ _ h
        cases bad with
        | true => cases h
        | false =>
          obtain ⟨s1,hs1,h⟩ := bind_success _ _ _ h
          obtain ⟨flat1,hflat,h⟩ := bind_success _ _ _ h
          obtain ⟨zs1,hzs,h⟩ := bind_success _ _ _ h
          cases h

/-- Every terminal branch frames start and the actual gathered line_z Vec. -/
theorem terminal_fields (ops : Ops CoreError) (start : Usize)
    (iter iter1 : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec M)
    (out : verifier.QueryGeometry)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter1))
    (h : verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat=ok (done (.Ok out))) : out.start=start ∧ out.line_z=zs := by
  unfold verifier.QueryGeometry.for_range_loop0.body at h
  rw [next,bind_tc_ok] at h
  obtain ⟨empty,he,h⟩ := bind_success _ _ _ h
  cases empty with
  | true => cases Result.ok.inj h; exact ⟨rfl,rfl⟩
  | false =>
    iterate 8 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
    cases Result.ok.inj h
    exact ⟨rfl,rfl⟩

#print axioms active_not_done
#print axioms terminal_fields
end AspisR1.Port4C_GeometryControl
end
