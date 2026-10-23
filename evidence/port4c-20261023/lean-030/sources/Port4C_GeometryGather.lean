import Port4C_GeometryStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)
variable {CoreError : Type}
abbrev M := aspis_core.field.M31

structure Row where
  x : M
  y : M
  lineX : M
  lineY : M
  lineZ : M

def Row.words (r : Row) : List M := [r.x,r.y,r.lineX,r.lineY,r.lineZ]

def Row.slice (r : Row) : Slice M := ⟨r.words,by simp [Row.words]; scalar_tac⟩

/-- An actual accepted gathering step appends all five tested words and the
same line_z. The domain/field calls stay visible as session A children. -/
theorem step (ops : Ops CoreError) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec M)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (h : verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∃ (r : Row) (u parent left right fibre fleft fright : Usize)
      (point : aspis_core.r0.domain.Point M) (square doubled one : M),
      iterOut=iter1 ∧
      lift (UScalar.cast .Usize query)=ok u ∧
      ops.op12 u=ok (.Ok fibre) ∧ ops.op15 fibre=ok point ∧
      u / 4#usize=ok parent ∧ left=Usize.wrapping_mul parent 4#usize ∧
      ops.op12 left=ok (.Ok fleft) ∧ ops.op14 fleft=ok r.lineX ∧
      right=Usize.wrapping_add left 3#usize ∧
      ops.op12 right=ok (.Ok fright) ∧ ops.op14 fright=ok r.lineY ∧
      r.x=point.x ∧ r.y=point.y ∧
      ops.op9 r.lineX r.lineX=ok square ∧ ops.op10 square=ok doubled ∧
      ops.op7=ok one ∧ ops.op8 doubled one=ok r.lineZ ∧
      (∀ x ∈ r.words, x≠0#u32) ∧
      flatOut.val=flat.val++r.words ∧ zsOut.val=zs.val++[r.lineZ] := by
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
          cases Result.ok.inj h
          have sl : s=(Row.mk point.x point.y lineX lineY lineZ).slice := (Result.ok.inj hs).symm
          have sl1 : s1=s := (Result.ok.inj hs1).symm.trans (Result.ok.inj hs)
          subst s1
          have hi : it=⟨s,0⟩ := (Result.ok.inj hit).symm
          subst it
          have nonzero := Port4C_GeometryStd.zero_test_false ops s after hzero
          have leftEq : left=Usize.wrapping_mul parent 4#usize := (Result.ok.inj hleft).symm
          have left1Eq : left1=left := (Result.ok.inj hleft1).symm.trans leftEq.symm
          subst left1
          refine ⟨⟨point.x,point.y,lineX,lineY,lineZ⟩,u,parent,left,right,fibre,fleft,fright,
            point,square,doubled,one,rfl,hu,hdom,hpoint,hparent,leftEq,hdomLeft,hlineX,
            (Result.ok.inj hright).symm,hdomRight,hlineY,rfl,rfl,hsquare,hdoubled,hone,hlineZ,?_,?_,?_⟩
          · intro x hx
            have member : x ∈ s.val := by rw [sl]; exact hx
            obtain ⟨i,hi,hx⟩ := List.getElem_of_mem member
            rw [←hx]
            exact nonzero i hi
          · have content := Port4C_GeometryStd.extend_fields flat flatOut s hflat
            rw [sl] at content
            exact content
          · exact MultiproofConeVecLaws.push_success zs zsOut lineZ hzs

#print axioms step
end AspisR1.Port4C_GeometryGather
end
