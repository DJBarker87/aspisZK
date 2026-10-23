import Port4C_GeometryControl
import Port4C_GeometryRange

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open Port4C_GeometryGather (Row)
variable {CoreError : Type}
abbrev M := aspis_core.field.M31

private theorem step_contents (ops : Ops CoreError) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec M)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (h : verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∃ r : Row, iterOut=iter1 ∧ (∀ x ∈ r.words, x≠0#u32) ∧
      flatOut.val=flat.val++r.words ∧ zsOut.val=zs.val++[r.lineZ] := by
  obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step ops start iter iter1 iterOut query zs zsOut flat flatOut next h
  rcases fields with ⟨hiter,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,nonzero,hflat,hzs⟩
  exact ⟨r,hiter,nonzero,hflat,hzs⟩

/-- Complete accepted gather traversal. The exact terminal buffers are
returned with the actual native inversion/grouping call on those buffers. -/
theorem accepted (ops : Ops CoreError) (start : Usize)
    (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec M)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (nonzero : ∀ x ∈ flat.val, x≠0#u32)
    (h : verifier.QueryGeometry.for_range_loop0 (Port4C_GeometryStd.install ops)
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      out.start=start ∧ out.line_z=zsFinal ∧
      zsFinal.val.length=zs.val.length+fuel ∧
      flatFinal.val.length=flat.val.length+5*fuel ∧
      (∀ x ∈ flatFinal.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.slice=iter.slice ∧ terminal.i=iter.slice.val.length := by
  induction fuel generalizing iter zs flat with
  | zero =>
    have inactive : ¬iter.i < iter.slice.val.length := by omega
    have next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rename_i active; exact False.elim (inactive active)
      · rfl
    unfold verifier.QueryGeometry.for_range_loop0 at h
    rw [Aeneas.Std.loop.eq_def] at h
    generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install ops) start iter zs flat = result at h
    cases result with
    | fail e => cases h
    | div => cases h
    | ok flow =>
      cases flow with
      | cont state =>
        rcases state with ⟨iter1,zs1,flat1⟩
        exact False.elim (Port4C_GeometryControl.terminal_not_cont ops start iter iter iter1
          zs flat zs1 flat1 next bodyRun)
      | done value =>
        cases Result.ok.inj h
        have fields := Port4C_GeometryControl.terminal_fields ops start iter iter zs flat out next bodyRun
        exact ⟨zs,flat,iter,fields.1,fields.2,by omega,by omega,nonzero,bodyRun,rfl,by omega⟩
  | succ fuel ih =>
    have active : iter.i < iter.slice.val.length := by omega
    let query := iter.slice.val[iter.i]
    let nextIter : core.slice.iter.Iter U32 := {iter with i:=iter.i+1}
    have next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,nextIter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rfl
      · rename_i inactive; exact False.elim (inactive active)
    unfold verifier.QueryGeometry.for_range_loop0 at h
    rw [Aeneas.Std.loop.eq_def] at h
    generalize bodyRun : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install ops) start iter zs flat = result at h
    cases result with
    | fail e => cases h
    | div => cases h
    | ok flow =>
      cases flow with
      | done value =>
        cases Result.ok.inj h
        exact False.elim (Port4C_GeometryControl.active_not_done ops start iter nextIter query zs flat out next bodyRun)
      | cont state =>
        rcases state with ⟨iter1,zs1,flat1⟩
        obtain ⟨r,same,hnz,hflat,hzs⟩ := step_contents ops start iter nextIter iter1 query zs zs1 flat flat1 next bodyRun
        subst iter1
        change verifier.QueryGeometry.for_range_loop0 (Port4C_GeometryStd.install ops)
          nextIter start zs1 flat1=ok (.Ok out) at h
        have safe : ∀ x ∈ flat1.val, x≠0#u32 := by
          intro x hx
          rw [hflat,List.mem_append] at hx
          exact hx.elim (nonzero x) (hnz x)
        obtain ⟨zsFinal,flatFinal,terminal,hstart,hline,hzl,hfl,hnz,ht,hs,hi⟩ :=
          ih nextIter zs1 flat1 (by dsimp [nextIter]; omega) safe h
        refine ⟨zsFinal,flatFinal,terminal,hstart,hline,?_,?_,hnz,ht,hs,hi⟩
        · rw [hzs,List.length_append,List.length_singleton] at hzl
          omega
        · rw [hflat,List.length_append] at hfl
          have rowLen : r.words.length=5 := by simp [Row.words]
          rw [rowLen] at hfl
          omega

#print axioms step_contents
#print axioms accepted
end AspisR1.Port4C_GeometryLoop
end
